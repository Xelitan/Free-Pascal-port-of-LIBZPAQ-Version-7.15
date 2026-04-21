# Pascal port of LIBZPAQ Version 7.15 (Aug. 17, 2016)
License: MIT

# Credits:

libdivsufsort (C) 2003-2008 Yuta Mori, license MIT

Some of the code for AES is from libtomcrypt 1.17 by Tom St. Denis, License: public domain

The Salsa20/8 code for Scrypt is by D. Bernstein, License: public domain

LibZPaq code by Matt Mahoney, License: public domain

LIBZPAQ is a library for compression and decompression
http://mattmahoney.net/zpaq/

# High-level classes

Usage- packing:

```
use ZpaqClasses;
[...]

p := TZpaqPacker.Create('pack.zpaq');  
p.SetMethod(1);

f := TFileStream.Create('input.txt', fmOpenRead);
p.AddFile(f, 'hello.txt'); 
f.Free;

p.Free;
```

Usage - listing and unpacking:

```
use ZpaqClasses;
[...]
u := TZpaqUnpacker.Create('pack.zpaq');
while u.NextEntry(name, size, date) do begin

  f := TFileStream.Create(name, fmCreate);
  u.Extract(f);
  f.Free;

end;
u.Free;                     
```

All at once:
```
use ZpaqSimple;
[...]
function CompressStreams(Infile, Outfile: TStream): Integer;
function DecompressStreams(Infile, Outfile: TStream): Integer;

function CompressFile(Infilename, Outfilename: String): Integer;
function DecompressFile(Infilename, Outfilename: String): Integer;

function Zpaq(Uncompressed: AnsiString): AnsiString;
function UnZpaq(Compressed: AnsiString): AnsiString;
```
