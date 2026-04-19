program zpaq;
{$mode objfpc}{$H+}

//Pascal port of LIBZPAQ Version 7.15 (Aug. 17, 2016)
//Port by www.xelitan.com
//License: MIT

//Credits:
//libdivsufsort (C) 2003-2008 Yuta Mori, license MIT
//Some of the code for AES is from libtomcrypt 1.17 by Tom St. Denis, License: public domain
//The Salsa20/8 code for Scrypt is by D. Bernstein, License: public domain
//LibZPaq code by Matt Mahoney, License: public domain
//LIBZPAQ is a library for compression and decompression
//http://mattmahoney.net/zpaq/


uses
  SysUtils, Classes, StrUtils, libzpaq;

{ ============================================================ }
{  TFileReader - reads from a file, supports seek/tell         }
{ ============================================================ }
type
  TFileReader = class(TZPAQLStream)
  private
    Fstream: TFileStream;
  public
    constructor Create(const filename: AnsiString);
    destructor  Destroy; override;
    function  get(): Integer; override;
    function  bread(buf: PU8; n: Integer): Integer; override;
    function  seek(pos: Int64): Boolean; override;
    function  tell(): Int64; override;
  end;

constructor TFileReader.Create(const filename: AnsiString);
begin
  inherited Create;
  Fstream := TFileStream.Create(filename, fmOpenRead or fmShareDenyWrite);
end;

destructor TFileReader.Destroy;
begin
  Fstream.Free;
  inherited Destroy;
end;

function TFileReader.get(): Integer;
var b: Byte;
begin
  if Fstream.Read(b, 1) = 1 then Result := b
  else Result := -1;
end;

function TFileReader.bread(buf: PU8; n: Integer): Integer;
begin
  Result := Fstream.Read(buf^, n);
end;

function TFileReader.seek(pos: Int64): Boolean;
begin
  try
    Fstream.Position := pos;
    Result := True;
  except
    Result := False;
  end;
end;

function TFileReader.tell(): Int64;
begin
  Result := Fstream.Position;
end;

{ ============================================================ }
{  TFileWriter - writes to a file                              }
{ ============================================================ }
type
  TFileWriter = class(TZPAQLStream)
  private
    Fstream: TFileStream;
  public
    constructor Create(const filename: AnsiString);
    destructor  Destroy; override;
    procedure put(c: Integer); override;
    procedure bwrite(buf: PU8; n: Integer); override;
  end;

constructor TFileWriter.Create(const filename: AnsiString);
begin
  inherited Create;
  Fstream := TFileStream.Create(filename, fmCreate);
end;

destructor TFileWriter.Destroy;
begin
  Fstream.Free;
  inherited Destroy;
end;

procedure TFileWriter.put(c: Integer);
var b: Byte;
begin
  b := c and $FF;
  Fstream.Write(b, 1);
end;

procedure TFileWriter.bwrite(buf: PU8; n: Integer);
begin
  if n > 0 then Fstream.Write(buf^, n);
end;

{ ============================================================ }
{  ExtractFilename helper (no extension)                        }
{ ============================================================ }
function GetBaseName(const path: AnsiString): AnsiString;
var i: Integer;
begin
  Result := ExtractFileName(path);
  i := Length(Result);
  while (i > 0) and (Result[i] <> '.') do Dec(i);
  if i > 1 then SetLength(Result, i-1);
end;

{ ============================================================ }
{  Journaling helper types and functions                        }
{ ============================================================ }

{ Little-endian 4-byte read from byte array }
function btoi(var p: PAnsiChar): Cardinal;
begin
  Result := Byte(p[0]) or (Byte(p[1]) shl 8) or
            (Byte(p[2]) shl 16) or (Byte(p[3]) shl 24);
  Inc(p, 4);
end;

{ Little-endian 8-byte read from byte array }
function btol(var p: PAnsiChar): Int64;
var lo, hi: Cardinal;
begin
  lo := btoi(p);
  hi := btoi(p);
  Result := Int64(lo) or (Int64(hi) shl 32);
end;

type
  { Fragment hash table entry }
  THTEntry = record
    sha1:  array[0..19] of Byte;
    usize: Integer;   { uncompressed size, -1 if streaming/unknown }
  end;
  THTArray = array of THTEntry;

  { Data block descriptor }
  TBlockEntry = record
    offset:  Int64;    { file offset of this 'd' block }
    start:   Cardinal; { first fragment index in ht[] }
    count:   Cardinal; { number of fragments in this block }
    bsize:   Cardinal; { compressed size of 'd' block }
  end;
  TBlockArray = array of TBlockEntry;

  { File entry from 'i' block }
  TDTEntry = record
    date:  Int64;
    fname: AnsiString;
    ptrs:  array of Cardinal; { fragment indices into ht[] }
  end;
  TDTArray = array of TDTEntry;

{ ============================================================ }
{  Usage                                                        }
{ ============================================================ }
procedure PrintUsage;
begin
  WriteLn('ZPAQ archiver (Free Pascal port of libzpaq v7.15)');
  WriteLn('');
  WriteLn('Usage:');
  WriteLn('  zpaq a <archive.zpaq> <file> [method]');
  WriteLn('       Compress <file> into <archive.zpaq>.');
  WriteLn('       method: 1..5 (default=3), or advanced like x3,1,4,0,3');
  WriteLn('');
  WriteLn('  zpaq l <archive.zpaq>');
  WriteLn('       List files stored in <archive.zpaq>.');
  WriteLn('');
  WriteLn('  zpaq x <archive.zpaq> [files...] [-to outdir]');
  WriteLn('       Decompress <archive.zpaq>. Output goes to current dir');
  WriteLn('       or to <outdir> if -to is specified.');
  WriteLn('       [files...] are optional filename filters (ignored).');
  WriteLn('');
  WriteLn('Examples:');
  WriteLn('  zpaq a backup.zpaq myfile.txt');
  WriteLn('  zpaq a backup.zpaq myfile.bin 5');
  WriteLn('  zpaq l backup.zpaq');
  WriteLn('  zpaq x backup.zpaq');
  WriteLn('  zpaq x backup.zpaq -to C:\restored\');
  Halt(1);
end;

{ ============================================================ }
{  Command: add (compress)                                      }
{ ============================================================ }
procedure CmdAdd(const archiveName, inputFile, method: AnsiString);
var
  reader: TFileReader;
  writer: TFileWriter;
  fname:  AnsiString;
  t1, t2: QWord;
  insize, outsize: Int64;
begin
  if not FileExists(inputFile) then begin
    WriteLn('ERROR: input file not found: ', inputFile);
    Halt(2);
  end;

  fname := ExtractFileName(inputFile);
  insize := 0;
  if FileExists(inputFile) then
    with TFileStream.Create(inputFile, fmOpenRead or fmShareDenyWrite) do
    try insize := Size; finally Free; end;

  WriteLn('Compressing "', inputFile, '" -> "', archiveName, '" method=', method);

  t1 := GetTickCount64;
  reader := TFileReader.Create(inputFile);
  writer := TFileWriter.Create(archiveName);
  try
    zpaq_compress(reader, writer, method, fname, '', True);
  finally
    reader.Free;
    writer.Free;
  end;
  t2 := GetTickCount64;

  outsize := 0;
  if FileExists(archiveName) then
    with TFileStream.Create(archiveName, fmOpenRead or fmShareDenyNone) do
    try outsize := Size; finally Free; end;

  WriteLn(Format('Done. %.0n bytes -> %.0n bytes in %.3f s',
    [Double(insize), Double(outsize), (t2-t1)/1000.0]));
end;

{ ============================================================ }
{  TOutputAdapter - collects decompress output to a file        }
{  named by the filename embedded in the archive segment        }
{ ============================================================ }
type
  TNamedOutput = class(TZPAQLStream)
  private
    Fwriter: TFileWriter;
    FoutDir: AnsiString;
    Fname:   AnsiString;
  public
    constructor Create(const outDir: AnsiString);
    destructor  Destroy; override;
    procedure openFile(const name: AnsiString);
    procedure closeFile();
    procedure put(c: Integer); override;
    procedure bwrite(buf: PU8; n: Integer); override;
  end;

constructor TNamedOutput.Create(const outDir: AnsiString);
begin
  inherited Create;
  if outDir <> '' then
    FoutDir := IncludeTrailingPathDelimiter(outDir)
  else
    FoutDir := '';
  Fwriter := nil;
end;

destructor TNamedOutput.Destroy;
begin
  closeFile();
  inherited Destroy;
end;

procedure TNamedOutput.openFile(const name: AnsiString);
var dir: AnsiString;
begin
  closeFile();
  if name = '' then begin
    WriteLn('Warning: unnamed segment, output discarded.');
    Exit;
  end;
  Fname := FoutDir + ExtractFileName(name);
  dir := ExtractFileDir(Fname);
  if (dir <> '') and not DirectoryExists(dir) then
    ForceDirectories(dir);
  WriteLn('  Extracting: ', Fname);
  Fwriter := TFileWriter.Create(Fname);
end;

procedure TNamedOutput.closeFile();
begin
  if Assigned(Fwriter) then begin
    Fwriter.Free;
    Fwriter := nil;
  end;
end;

procedure TNamedOutput.put(c: Integer);
begin
  if Assigned(Fwriter) then Fwriter.put(c);
end;

procedure TNamedOutput.bwrite(buf: PU8; n: Integer);
begin
  if Assigned(Fwriter) then Fwriter.bwrite(buf, n);
end;

{ ============================================================ }
{  TMemWriter - accumulates decompressed bytes in memory        }
{ ============================================================ }
type
  TMemWriter = class(TZPAQLStream)
  private
    FData: TBytes;
    FSize: Integer;
  public
    constructor Create(capacity: Integer = 65536);
    procedure put(c: Integer); override;
    procedure bwrite(buf: PU8; n: Integer); override;
    procedure reset();
    function  size(): Integer; inline;
    function  dataPtr(): PU8; inline;
  end;

constructor TMemWriter.Create(capacity: Integer);
begin
  inherited Create;
  FSize := 0;
  SetLength(FData, capacity);
end;

procedure TMemWriter.put(c: Integer);
begin
  if FSize >= Length(FData) then
    SetLength(FData, Length(FData) * 2 + 1);
  FData[FSize] := Byte(c and $FF);
  Inc(FSize);
end;

procedure TMemWriter.bwrite(buf: PU8; n: Integer);
begin
  if n <= 0 then Exit;
  if FSize + n > Length(FData) then begin
    while FSize + n > Length(FData) do
      SetLength(FData, Length(FData) * 2 + n);
  end;
  Move(buf^, FData[FSize], n);
  Inc(FSize, n);
end;

procedure TMemWriter.reset();
begin
  FSize := 0;
end;

function TMemWriter.size(): Integer;
begin
  Result := FSize;
end;

function TMemWriter.dataPtr(): PU8;
begin
  if FSize > 0 then Result := @FData[0]
  else Result := nil;
end;

{ ============================================================ }
{  Journaling extraction: scan pass                             }
{ ============================================================ }

{ Run one scan pass over the archive starting from current reader position.
  Returns True if a 'c' block was processed and we seeked past 'd' blocks
  (caller must re-enter with fresh decompressor). }
function ScanPass(
  reader: TFileReader;
  memOut: TMemWriter;
  var ht: THTArray;
  var htCount: Integer;
  var blocks: TBlockArray;
  var blockCount: Integer;
  var files: TDTArray;
  var fileCount: Integer;
  var isJournaling: Boolean;
  var data_offset: Int64): Boolean;
var
  dec:       TDecompresser;
  fname:     TStringBuffer;
  comment:   TStringBuffer;
  fnStr, cmStr: AnsiString;
  blockType: AnsiChar;
  n:         Cardinal;
  bsize:     Cardinal;
  jmp:       Int64;
  s:         PAnsiChar;
  i:         Integer;
  ch:        AnsiChar;
  date:      Int64;
  na, ni:    Cardinal;
  j:         Integer;
  num:       Int64;
  ptrArr:    array of Cardinal;
  p, pEnd:   PAnsiChar;
  cmLen:     Integer;
  didSeek:   Boolean;
begin
  Result := False;
  didSeek := False;

  dec     := TDecompresser.Create;
  fname   := TStringBuffer.Create;
  comment := TStringBuffer.Create;
  try
    dec.setInput(reader);
    dec.setOutput(memOut);

    while (not didSeek) and dec.findBlock(nil) do begin
      while (not didSeek) and dec.findFilename(fname) do begin
        { get filename string }
        fnStr := '';
        if fname.size() > 0 then
          SetString(fnStr, fname.c_str(), fname.size());
        fname.resize(0);

        { read comment }
        comment.resize(0);
        dec.readComment(comment);
        cmStr := '';
        if comment.size() > 0 then
          SetString(cmStr, comment.c_str(), comment.size());

        { Check for JIDAC journaling block:
          filename = 28 chars starting "jDC"
          comment ends with "jDC"#1  (j + D + C + chr(1)) }
        cmLen := Length(cmStr);
        if (cmLen >= 5) and
           (Length(fnStr) = 28) and
           (fnStr[1] = 'j') and (fnStr[2] = 'D') and (fnStr[3] = 'C') and
           (cmStr[cmLen-3] = 'j') and
           (cmStr[cmLen-2] = 'D') and
           (cmStr[cmLen-1] = 'C') and
           (Ord(cmStr[cmLen]) = 1) then
        begin
          isJournaling := True;
          blockType := fnStr[18]; { 0-indexed pos 17 = 1-indexed pos 18 }

          { Read fragment start number from filename[19..28] }
          num := 0;
          for i := 19 to 28 do begin
            ch := fnStr[i];
            if (ch >= '0') and (ch <= '9') then
              num := num * 10 + (Ord(ch) - Ord('0'));
          end;

          if blockType in ['c','h','i'] then begin
            { Decompress this index/control block into memOut }
            memOut.reset();
            dec.decompress(-1);
            dec.readSegmentEnd(nil);

            if blockType = 'c' then begin
              { Transaction header: first 8 bytes = jmp (total 'd' block size) }
              if memOut.size() >= 8 then begin
                s := PAnsiChar(memOut.dataPtr());
                jmp := btol(s);
                if jmp >= 0 then begin
                  { data_offset = start of first 'd' block = position after 'c' block }
                  data_offset := dec.getPos();
                  if jmp > 0 then begin
                    { Seek past all 'd' blocks; must recreate decompressor }
                    reader.seek(data_offset + jmp);
                    didSeek := True;
                  end;
                end else
                  WriteLn('Warning: incomplete transaction ignored');
              end;
            end

            else if blockType = 'h' then begin
              { Fragment hash table: bsize[4] + (sha1[20]+usize[4])*n }
              if (memOut.size() >= 4) and ((memOut.size() - 4) mod 24 = 0) then begin
                n := Cardinal((memOut.size() - 4) div 24);
                s := PAnsiChar(memOut.dataPtr());
                bsize := btoi(s);

                { Grow ht[] to accommodate fragments num..num+n-1 }
                while htCount <= Integer(num + n) - 1 do begin
                  if htCount >= Length(ht) then
                    SetLength(ht, Length(ht) * 2 + 64);
                  FillChar(ht[htCount], SizeOf(THTEntry), 0);
                  ht[htCount].usize := -1;
                  Inc(htCount);
                end;

                { Add block entry }
                if blockCount >= Length(blocks) then
                  SetLength(blocks, Length(blocks) * 2 + 16);
                blocks[blockCount].offset := data_offset;
                blocks[blockCount].start  := Cardinal(num);
                blocks[blockCount].count  := n;
                blocks[blockCount].bsize  := bsize;
                Inc(blockCount);

                { Read fragment SHA1 and usize }
                for i := 0 to Integer(n) - 1 do begin
                  if Integer(num) + i >= Length(ht) then
                    SetLength(ht, Integer(num) + i + 64);
                  Move(s^, ht[num + i].sha1[0], 20);
                  Inc(s, 20);
                  ht[num + i].usize := Integer(btoi(s));
                  if Integer(num) + i + 1 > htCount then
                    htCount := Integer(num) + i + 1;
                end;

                data_offset := data_offset + bsize;
              end;
            end

            else if blockType = 'i' then begin
              { File index: (date[8] name\0 na[4] attr[na] ni[4] ptr[4]...)* }
              p    := PAnsiChar(memOut.dataPtr());
              pEnd := p + memOut.size();
              while p + 9 <= pEnd do begin
                date := btol(p);
                i := 0;
                while (p + i < pEnd) and (p[i] <> #0) do Inc(i);
                fnStr := '';
                if i > 0 then
                  SetString(fnStr, p, i);
                Inc(p, i + 1);
                if p > pEnd then Break;

                if date <> 0 then begin
                  if p + 4 > pEnd then Break;
                  na := btoi(p);
                  if p + na > pEnd then Break;
                  Inc(p, na);  { skip attributes }
                  if p + 4 > pEnd then Break;
                  ni := btoi(p);
                  if p + Int64(ni) * 4 > pEnd then Break;
                  SetLength(ptrArr, ni);
                  for j := 0 to Integer(ni) - 1 do
                    ptrArr[j] := btoi(p);

                  if fileCount >= Length(files) then
                    SetLength(files, Length(files) * 2 + 16);
                  files[fileCount].date  := date;
                  files[fileCount].fname := fnStr;
                  files[fileCount].ptrs  := Copy(ptrArr, 0, ni);
                  Inc(fileCount);
                end;
              end;
            end;

          end else begin
            { 'd' type or unknown during scan - just skip }
            dec.readSegmentEnd(nil);
          end;

        end else begin
          { Not a journaling block -> streaming format, skip }
          dec.readSegmentEnd(nil);
        end;

      end; { while findFilename }
    end; { while findBlock }

    Result := didSeek;
  finally
    comment.Free;
    fname.Free;
    dec.Free;
  end;
end;

procedure ScanJournaling(
  reader: TFileReader;
  var ht: THTArray;
  var htCount: Integer;
  var blocks: TBlockArray;
  var blockCount: Integer;
  var files: TDTArray;
  var fileCount: Integer;
  var isJournaling: Boolean);
var
  memOut:       TMemWriter;
  data_offset:  Int64;
  didSeek:      Boolean;
begin
  isJournaling := False;
  htCount      := 1;  { index 0 unused (sentinel) }
  blockCount   := 0;
  fileCount    := 0;
  data_offset  := 0;

  memOut := TMemWriter.Create(65536);
  try
    { Loop: each iteration is one scan pass with a fresh decompressor.
      If ScanPass returns True, a seek happened and we loop again from
      the new position with a fresh decompressor (mimics C++ goto endblock). }
    repeat
      didSeek := ScanPass(reader, memOut, ht, htCount, blocks, blockCount,
                          files, fileCount, isJournaling, data_offset);
    until not didSeek;
  finally
    memOut.Free;
  end;
end;

{ ============================================================ }
{  Journaling extraction: extract pass                          }
{ ============================================================ }

{ Find the block index that contains fragment fragIdx. Returns -1 if not found. }
function FindBlock(fragIdx: Cardinal; const blocks: TBlockArray; blockCount: Integer): Integer;
var bi: Integer;
begin
  for bi := 0 to blockCount - 1 do
    if (fragIdx >= blocks[bi].start) and
       (fragIdx < blocks[bi].start + blocks[bi].count) then begin
      Result := bi; Exit;
    end;
  Result := -1;
end;

{ Compute byte offset of fragment fragIdx within its decompressed block. }
function FragmentOffset(fragIdx: Cardinal; blockIdx: Integer;
  const ht: THTArray; const blocks: TBlockArray): Int64;
var k: Integer; sz: Integer;
begin
  Result := 0;
  for k := 0 to Integer(fragIdx - blocks[blockIdx].start) - 1 do begin
    sz := ht[blocks[blockIdx].start + k].usize;
    if sz > 0 then Result := Result + sz;
  end;
end;

procedure ExtractJournaledFiles(
  archiveName: AnsiString;
  const ht: THTArray;
  htCount: Integer;
  const blocks: TBlockArray;
  blockCount: Integer;
  const files: TDTArray;
  fileCount: Integer;
  const outDir: AnsiString);
var
  fi, pi:       Integer;
  ptr:          Cardinal;
  blockIdx:     Integer;
  fragSize:     Integer;
  reader2:      TFileReader;
  dec2:         TDecompresser;
  memOut2:      TMemWriter;
  outPath:      AnsiString;
  outDir2:      AnsiString;
  dirPart:      AnsiString;
  outFile:      TFileStream;
  bytesNeeded:  Int64;
  k:            Integer;
  fragOff:      Int64;
  lastBlockIdx: Integer;  { block decompressed in current iteration }
begin
  if outDir <> '' then
    outDir2 := IncludeTrailingPathDelimiter(outDir)
  else
    outDir2 := '';

  for fi := 0 to fileCount - 1 do begin
    if files[fi].date = 0 then Continue;  { deletion record }

    { Determine output path }
    outPath := outDir2 + ExtractFileName(files[fi].fname);
    dirPart := ExtractFileDir(outPath);
    if (dirPart <> '') and not DirectoryExists(dirPart) then
      ForceDirectories(dirPart);

    if Length(files[fi].ptrs) = 0 then begin
      WriteLn('  Extracting (empty): ', outPath);
      TFileStream.Create(outPath, fmCreate).Free;
      Continue;
    end;

    WriteLn('  Extracting: ', outPath);
    outFile := TFileStream.Create(outPath, fmCreate);
    try
      lastBlockIdx := -1;
      reader2 := nil;
      memOut2 := nil;
      dec2    := nil;

      for pi := 0 to Length(files[fi].ptrs) - 1 do begin
        ptr := files[fi].ptrs[pi];
        if (ptr = 0) or (Integer(ptr) >= htCount) then Continue;

        { Find which block contains this fragment }
        blockIdx := FindBlock(ptr, blocks, blockCount);
        if blockIdx < 0 then begin
          WriteLn('  Warning: fragment ', ptr, ' not found in any block');
          Continue;
        end;

        { Decompress block if it's different from the last one }
        if blockIdx <> lastBlockIdx then begin
          { Free previous }
          if dec2    <> nil then dec2.Free;
          if memOut2 <> nil then memOut2.Free;
          if reader2 <> nil then reader2.Free;

          { Compute total decompressed size needed for this block }
          bytesNeeded := 0;
          for k := 0 to Integer(blocks[blockIdx].count) - 1 do begin
            if Integer(blocks[blockIdx].start) + k < htCount then begin
              fragSize := ht[blocks[blockIdx].start + k].usize;
              if fragSize > 0 then Inc(bytesNeeded, fragSize);
            end;
          end;

          reader2 := TFileReader.Create(archiveName);
          memOut2 := TMemWriter.Create(Integer(bytesNeeded) + 1024);
          dec2    := TDecompresser.Create;
          reader2.seek(blocks[blockIdx].offset);
          dec2.setInput(reader2);
          dec2.setOutput(memOut2);

          if dec2.findBlock(nil) then begin
            while dec2.findFilename(nil) do begin
              dec2.readComment(nil);
              while (memOut2.size() < bytesNeeded) and
                    dec2.decompress(1 shl 14) do ;
              if memOut2.size() >= bytesNeeded then Break;
              dec2.readSegmentEnd(nil);
            end;
          end;

          lastBlockIdx := blockIdx;
        end;

        { Write this fragment to output }
        fragOff  := FragmentOffset(ptr, blockIdx, ht, blocks);
        fragSize := ht[ptr].usize;
        if fragSize > 0 then begin
          if (memOut2 <> nil) and
             (fragOff + fragSize <= memOut2.size()) then
            outFile.Write(memOut2.dataPtr()[fragOff], fragSize)
          else
            WriteLn('  Warning: fragment ', ptr, ' out of range in decompressed block');
        end;
      end; { for pi }

      { Free last block }
      if dec2    <> nil then dec2.Free;
      if memOut2 <> nil then memOut2.Free;
      if reader2 <> nil then reader2.Free;
    finally
      outFile.Free;
    end;
  end; { for fi }
end;

{ ============================================================ }
{  FormatDate - convert ZPAQ date integer to readable string    }
{ ============================================================ }
{ ZPAQ date format (64-bit): YYYYMMDDHHmmss packed as decimal  }
{ i.e. the integer 20260418153045 means 2026-04-18 15:30:45    }
function FormatZpaqDate(d: Int64): AnsiString;
var
  s, ss, mi, hh, dd, mo, yy: Integer;
begin
  if d = 0 then begin Result := '                   '; Exit; end;
  s  :=  d mod 100; d := d div 100;
  mi :=  d mod 100; d := d div 100;
  hh :=  d mod 100; d := d div 100;
  dd :=  d mod 100; d := d div 100;
  mo :=  d mod 100; d := d div 100;
  yy :=  Integer(d);
  ss := s;  { suppress 'unused' hint }
  Result := Format('%.4d-%.2d-%.2d %.2d:%.2d:%.2d', [yy, mo, dd, hh, mi, ss]);
end;

{ ============================================================ }
{  CmdList - list archive contents                              }
{ ============================================================ }
procedure CmdList(const archiveName: AnsiString);
var
  reader:      TFileReader;
  dec:         TDecompresser;
  fnameStream: TStringBuffer;
  fname:       AnsiString;
  { journaling data }
  ht:          THTArray;
  blocks:      TBlockArray;
  files:       TDTArray;
  htCount, blockCount, fileCount: Integer;
  isJournaling: Boolean;
  fi, pi:      Integer;
  totalSize:   Int64;
  fsize:       Int64;
  ptr:         Cardinal;
begin
  if not FileExists(archiveName) then begin
    WriteLn('ERROR: archive not found: ', archiveName);
    Halt(2);
  end;

  SetLength(ht,     64);
  SetLength(blocks, 16);
  SetLength(files,  16);
  htCount := 0; blockCount := 0; fileCount := 0;
  isJournaling := False;

  reader := TFileReader.Create(archiveName);
  try
    ScanJournaling(reader, ht, htCount, blocks, blockCount,
                   files, fileCount, isJournaling);
  finally
    reader.Free;
  end;

  if isJournaling then begin
    { Journaling format: we have a full file list with dates and sizes }
    WriteLn(Format('%-19s  %12s  %s', ['Date/Time', 'Size', 'Filename']));
    WriteLn(StringOfChar('-', 72));
    totalSize := 0;
    for fi := 0 to fileCount - 1 do begin
      if files[fi].date = 0 then Continue;  { deletion record }
      fsize := 0;
      for pi := 0 to Length(files[fi].ptrs) - 1 do begin
        ptr := files[fi].ptrs[pi];
        if (ptr > 0) and (Integer(ptr) < htCount) and (ht[ptr].usize > 0) then
          Inc(fsize, ht[ptr].usize);
      end;
      WriteLn(Format('%-19s  %12d  %s',
        [FormatZpaqDate(files[fi].date), fsize, files[fi].fname]));
      Inc(totalSize, fsize);
    end;
    WriteLn(StringOfChar('-', 72));
    WriteLn(Format('%d file(s), %d bytes total', [fileCount, totalSize]));
  end else begin
    { Streaming format: scan for filenames in segment headers }
    WriteLn(Format('%-19s  %s', ['Size', 'Filename']));
    WriteLn(StringOfChar('-', 50));
    fileCount := 0;
    reader   := TFileReader.Create(archiveName);
    dec      := TDecompresser.Create;
    fnameStream := TStringBuffer.Create;
    try
      dec.setInput(reader);
      dec.setOutput(nil);
      while dec.findBlock(nil) do begin
        while dec.findFilename(fnameStream) do begin
          fname := '';
          if fnameStream.size() > 0 then
            SetString(fname, fnameStream.c_str(), fnameStream.size());
          fnameStream.resize(0);
          dec.readComment(nil);
          WriteLn(Format('%-19s  %s', ['(streaming)', fname]));
          Inc(fileCount);
          while dec.decompress(-1) do ;
          dec.readSegmentEnd(nil);
        end;
      end;
    finally
      fnameStream.Free;
      dec.Free;
      reader.Free;
    end;
    WriteLn(StringOfChar('-', 50));
    WriteLn(Format('%d file(s)', [fileCount]));
  end;
end;

{ ============================================================ }
{  CmdExtract - streaming or journaling                         }
{ ============================================================ }
procedure CmdExtract(const archiveName, outDir: AnsiString);
var
  reader:      TFileReader;
  namedOut:    TNamedOutput;
  dec:         TDecompresser;
  fnameStream: TStringBuffer;
  cmtStream:   TStringBuffer;
  fname:       AnsiString;
  t1, t2:      QWord;
  { journaling data }
  ht:          THTArray;
  blocks:      TBlockArray;
  files:       TDTArray;
  htCount, blockCount, fileCount: Integer;
  isJournaling: Boolean;
begin
  if not FileExists(archiveName) then begin
    WriteLn('ERROR: archive not found: ', archiveName);
    Halt(2);
  end;

  WriteLn('Decompressing "', archiveName, '" to "',
    IfThen(outDir = '', '.', outDir), '"');

  t1 := GetTickCount64;

  { ---- Pass 0: quick peek to detect journaling ---- }
  { We scan with a fresh reader to detect format, then either do
    journaling extraction or streaming extraction. }

  SetLength(ht,     64);
  SetLength(blocks, 16);
  SetLength(files,  16);
  htCount := 0; blockCount := 0; fileCount := 0;
  isJournaling := False;

  reader := TFileReader.Create(archiveName);
  try
    ScanJournaling(reader, ht, htCount, blocks, blockCount,
                   files, fileCount, isJournaling);
  finally
    reader.Free;
  end;

  if isJournaling then begin
    { ---- Journaling extraction ---- }
    WriteLn(Format('Journaling archive: %d fragment(s), %d block(s), %d file(s)',
      [htCount - 1, blockCount, fileCount]));
    ExtractJournaledFiles(archiveName, ht, htCount, blocks, blockCount,
                          files, fileCount, outDir);
  end else begin
    { ---- Streaming extraction (original approach) ---- }
    reader   := TFileReader.Create(archiveName);
    namedOut := TNamedOutput.Create(outDir);
    dec      := TDecompresser.Create;
    fnameStream := TStringBuffer.Create;
    cmtStream   := TStringBuffer.Create;
    try
      dec.setInput(reader);
      dec.setOutput(namedOut);

      while dec.findBlock(nil) do begin
        while dec.findFilename(fnameStream) do begin
          fname := '';
          if fnameStream.c_str() <> nil then
            SetString(fname, fnameStream.c_str(), fnameStream.size());
          namedOut.openFile(fname);
          fnameStream.resize(0);

          cmtStream.resize(0);
          dec.readComment(cmtStream);
          while dec.decompress(-1) do ;
          dec.readSegmentEnd(nil);
          namedOut.closeFile();
        end;
      end;
    finally
      cmtStream.Free;
      fnameStream.Free;
      dec.Free;
      namedOut.Free;
      reader.Free;
    end;
  end;

  t2 := GetTickCount64;
  WriteLn(Format('Done in %.3f s', [(t2-t1)/1000.0]));
end;

{ ============================================================ }
{  Main                                                         }
{ ============================================================ }
var
  cmd:     AnsiString;
  archive: AnsiString;
  method:  AnsiString;
  outDir:  AnsiString;
  i:       Integer;
begin
  if ParamCount < 2 then PrintUsage;

  cmd     := LowerCase(ParamStr(1));
  archive := ParamStr(2);

  if (cmd = 'l') or (cmd = 'list') then begin
    { zpaq l archive }
    try
      CmdList(archive);
    except
      on E: Exception do begin
        WriteLn('ERROR: ', E.Message);
        Halt(3);
      end;
    end;
  end
  else if cmd = 'a' then begin
    { zpaq a archive file [method] }
    if ParamCount < 3 then begin
      WriteLn('ERROR: missing input file for "a" command.');
      PrintUsage;
    end;
    method := '3';
    if ParamCount >= 4 then method := ParamStr(4);
    try
      CmdAdd(archive, ParamStr(3), method);
    except
      on E: Exception do begin
        WriteLn('ERROR: ', E.Message);
        Halt(3);
      end;
    end;
  end
  else if cmd = 'x' then begin
    { zpaq x archive [files...] [-to outdir]
      Scan all arguments for "-to"; everything else is a file filter (ignored). }
    outDir := '';
    i := 3;
    while i <= ParamCount do begin
      if LowerCase(ParamStr(i)) = '-to' then begin
        if i < ParamCount then begin
          outDir := ParamStr(i + 1);
          Inc(i, 2);
        end else
          Inc(i);
      end else
        Inc(i);  { file filter - skip }
    end;
    try
      CmdExtract(archive, outDir);
    except
      on E: Exception do begin
        WriteLn('ERROR: ', E.Message);
        Halt(3);
      end;
    end;
  end
  else begin
    WriteLn('Unknown command: ', cmd);
    PrintUsage;
  end;
end.
