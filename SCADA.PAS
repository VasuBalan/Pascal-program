{$R-}    {Range checking off}
{$B+}    {Boolean complete evaluation on}
{$S+}    {Stack checking on}
{$I+}    {I/O checking on}
{$N-}    {No numeric coprocessor}
{$M 65500,16384,655360} {Turbo 3 default stack and heap}

program scada(input,output,inputfile,outfile);

{   Program to simulate Supervisory Control And Data Acquision System     }
{   that brings data from power system into a state estimator.            }



Uses
  Crt;

const
      maxbus=25;
      maxline=40;
      maxline2=80;
      maxtran=10;
      maxzvmag=25;
      maxzvang=25;
      maxzinjec=25;
      maxzflow=80;
      ioval : integer = 0;
      ioerr : boolean = false;
      dpr : real = 57.29577951;
type
        polar = record
                m,a:real;
                end;
        complex=record
                r,i:real;
                end;
        rbv = record
              bus:integer;
              stddev,z:real;
              end;
        rbi = record
              bus:integer;
              stddev,z:complex;
              end;
        rl = record
             branch:integer;
             stddev,z:complex;
             end;
        lntype=packed array [1..4] of char;
        acb=array [1..maxbus] of complex;
        apb=array [1..maxbus] of polar;
        acl2=array [1..maxline2] of complex;
        aib=array [1..maxbus] of integer;
        ail2=array [1..maxline2] of integer;
        art=array [1..maxtran] of real;
        ait=array [1..maxtran] of integer;
        arl2=array [1..maxline2] of real;
        all2=array [1..maxline2] of lntype;
        arbvzvm=array [1..maxzvmag] of rbv;
        arbvzva=array [1..maxzvang] of rbv;
        arbizi=array [1..maxzinjec] of rbi;
        arlzf=array [1..maxzflow] of rl;
var
    debug:boolean;
    numbus,numlines,numline2,numtran:integer;
    nummeaslines,numvoltmag,numvoltang:integer;
    numinjec,numflow:integer;
    linenumber:integer;
    zero:complex;
    inputfile,outfile:text;
    title1,title2:string[80];
    filename:string[25];
    ec:acb;
    ep:apb;
    bound:aib;
    frombus,tobus:ail2;
    y,ys:acl2;
    tran_pointer:ail2;
    tapbus:ait;
    tapratio:art;
    r,x,bcap:arl2;
    linetype:all2;
    zvoltmag:arbvzvm;
    zvoltang:arbvzva;
    zinjec:arbizi;
    zflow:arlzf;

label quit;

{ ------------------------------------------------------------------}
procedure cadd(var c:complex; a,b:complex);
begin { cadd }
  c.r := a.r + b.r;
  c.i := a.i + b.i;
end; { cadd }
procedure csub(var c:complex; a,b:complex);
begin { csub }
  c.r := a.r - b.r;
  c.i := a.i - b.i;
end; { csub }
procedure conj(var c:complex; a:complex);
begin { conj }
  c.r := a.r;
  c.i := -a.i;
end; { conj }
procedure cmult(var c:complex; a,b:complex);
begin { cmult }
  c.r := a.r * b.r - a.i * b.i;
  c.i := a.r * b.i + a.i * b.r;
end; { cmult }
procedure scale(var c:complex; a:real; b:complex);
begin { scale }
  c.r := a * b.r;
  c.i := a * b.i;
end; { scale }
procedure cdiv(var c:complex; a,b:complex);
var
    rbmag2:real;
begin { cdiv }
  rbmag2 := 1.0 / (b.r * b.r + b.i * b.i);
  c.r := rbmag2 * (a.r * b.r + a.i * b.i);
  c.i := rbmag2 * (b.r * a.i - a.r * b.i);
end; { cdiv }
procedure recip(var c:complex; a:complex);
var
    ramag2:real;
begin { recip }
  ramag2 := 1.0 / (a.r * a.r + a.i * a.i);
  c.r := ramag2 * a.r;
  c.i := - ramag2 * a.i;
end; { recip }

{----------------------------------------------------------------------------}
{$I-,R-}
{ <f> <s>   IO Check routine }
procedure IOCheck( linenumber : integer );

      {This routine sets IOErr equal to IOresult, then sets
       IOFlag accordingly.  It also prints out a message on
       the 24th line of the screen.}

var
  Ch                   : Char;
begin
  IOVal := IOresult;
  IOErr := (IOVal <> 0);
  GotoXY(1,24); ClrEol;        { Clear error line in any case }
  if IOErr then begin
    Write(Chr(7));
    case IOVal of
        2  :  Writeln('File does not exist');
        3  :  Writeln('Path not found  ');
        4  :  Writeln('Too many files open ');
        5  :  Writeln('File access denied ');
       12  :  Writeln('Invalid file access code ');
       15  :  Writeln('Invalid drive number ');
      100  :  Writeln('Disk read error ');
      101  :  Writeln('Disk write error ');
      102  :  Writeln('File not assigned ');
      103  :  Writeln('File not open');
      104  :  Writeln('File not open for input');
      105  :  Writeln('File not open for output');
      106  :  Writeln('Error in numeric format');
      150  :  Writeln('Disk is write protected');
      151  :  Writeln('Unknown unit');
      152  :  Writeln('Drive not ready');
      153  :  Writeln('Unknown command ');
      154  :  Writeln('CRC error in data ');
      155  :  Writeln('Bad drive structure length ');
      156  :  Writeln('Disk seek error ');
      157  :  Writeln('Unknown media type ');
      158  :  Writeln('Selector not found ');
      159  :  Writeln('Printer out of paper ');
      160  :  Writeln('Device write fault ');
      161  :  Writeln('Device read fault ');
      162  :  Writeln('Hardware failure ');
    else      Writeln('Unknown I/O error:  ',IOVal:3)
    end;
    writeln( ' error on line ', linenumber, ' of input file ')
  end
end; { of proc IOCheck }

{ ------------------------------------------------------------------}
procedure input_solution;

var
    i,j:integer;
    filename:string[25];

label quit;

begin { input_solution }
  writeln;
  write('Enter name of solution data file :');
  readln(filename);
  writeln;
  linenumber := 0;
  assign( inputfile, filename );      iocheck( linenumber);
                                      if ioerr then goto quit;

  reset( inputfile );                 iocheck( linenumber);
                                      if ioerr then goto quit;


  { skip titles }

  linenumber := linenumber + 1;
  readln(inputfile);            iocheck( linenumber);
                                if ioerr then goto quit;


  linenumber := linenumber + 1;
  readln(inputfile);            iocheck( linenumber);
                                if ioerr then goto quit;


  { read bus solution data }

  for i:=1 to numbus do
    begin
      read(inputfile,j);              iocheck( linenumber);
                                      if ioerr then goto quit;

      if (1<=j) and (j<=numbus) then with ec[j],ep[j] do
        begin
        readln(inputfile,m,a);
        r:=m*cos(a);
        i:=m*sin(a);
        end
      else
        begin
        writeln;
        writeln('ERROR - Bus ',j:1,' is a invalid bus number.');
        writeln;
        end;
    end;

  close ( inputfile );

quit:

end; { input_solution }
{----------------------------------------------------------------------------}
procedure input_lfdata;

type
     arl=array [1..maxline] of real;
     ail=array [1..maxline] of integer;
     all=array [1..maxline] of lntype;
var
    i,j,k:integer;
    temp_frombus,temp_tobus,temp_tran_pointer:ail;
    temp_r,temp_x,temp_bcap,temp_linelimit:arl;
    temp_linetype:all;
    z:complex;
    nulinteger,numgen:integer;
    nulreal:real;

label quit;

procedure readlinetype(i:integer);
var
    j:integer;
    ch:char;

label quit;

begin { readlinetype }
  repeat
    read( inputfile, ch );            iocheck( linenumber);
                                      if ioerr then goto quit;

  until ch<>' ';
  temp_linetype[i][1]:=ch;
  for j:=2 to 4 do
    begin
    read( inputfile, temp_linetype[i][j]);     iocheck( linenumber);
                                               if ioerr then goto quit;
    end;

quit:

end; { readlinetype }

begin { input_lfdata }
  writeln;
  write('Enter name of load flow data file :');
  readln(filename);
  writeln;
  linenumber := 0;
  assign( inputfile, filename );      iocheck( linenumber);
                                      if ioerr then goto quit;

  reset( inputfile );                 iocheck( linenumber);
                                      if ioerr then goto quit;


  { read titles and constants }

  linenumber := linenumber + 1;
  readln( inputfile, title1 );      iocheck( linenumber);
                                    if ioerr then goto quit;


  linenumber := linenumber + 1;
  readln( inputfile, title2 );      iocheck( linenumber);
                                    if ioerr then goto quit;


  linenumber := linenumber + 1;
  readln( inputfile, numbus );      iocheck( linenumber);
                                    if ioerr then goto quit;


  linenumber := linenumber + 1;
  readln( inputfile, numgen );      iocheck( linenumber);
                                    if ioerr then goto quit;


  linenumber := linenumber + 1;
  readln( inputfile, numlines );    iocheck( linenumber);
                                    if ioerr then goto quit;


  linenumber := linenumber + 1;
  readln( inputfile );              iocheck( linenumber);
                                    if ioerr then goto quit;


  { skip bus data }

  for i := 1 to numbus do
    begin
    linenumber := linenumber + 1;
    readln( inputfile );              iocheck( linenumber);
                                      if ioerr then goto quit;

    end;

  { skip generator data }

  for i := 1 to numgen do
    begin
    linenumber := linenumber + 1;
    readln( inputfile );              iocheck( linenumber);
                                      if ioerr then goto quit;

    end;

  { read line data }

  numtran := 0;
  for i := 1 to numlines do
    begin
    linenumber := linenumber + 1;
    read( inputfile, temp_frombus[i] );        iocheck( linenumber);
                                               if ioerr then goto quit;

    read( inputfile, temp_tobus[i] );          iocheck( linenumber);
                                               if ioerr then goto quit;

    read( inputfile, temp_r[i] );              iocheck( linenumber);
                                               if ioerr then goto quit;

    read( inputfile, temp_x[i] );              iocheck( linenumber);
                                               if ioerr then goto quit;

    read( inputfile, temp_bcap[i] );           iocheck( linenumber);
                                               if ioerr then goto quit;

    read( inputfile, nulreal);                 iocheck( linenumber);
                                               if ioerr then goto quit;

    readlinetype(i);
    if temp_linetype[i] = 'TRAN' then
      begin
      numtran := numtran + 1;
      read( inputfile, tapbus[ numtran ] );    iocheck( linenumber);
                                               if ioerr then goto quit;

      read( inputfile, nulinteger );           iocheck( linenumber);
                                               if ioerr then goto quit;

      read( inputfile, tapratio[ numtran ] );  iocheck( linenumber);
                                               if ioerr then goto quit;

      temp_tran_pointer[ i ] := numtran
      end;
    readln( inputfile );                       iocheck( linenumber);
                                               if ioerr then goto quit;

    end;

  close ( inputfile );

  { build double order line tables }

  k := 1;

  for i := 1 to numbus do
    begin
    bound[i]:=k;
    for j := 1 to numlines do
      begin
      if temp_frombus[j] = i then
        begin
        frombus[k] := temp_frombus[j];
        tobus[k] := temp_tobus[j];
        r[k] := temp_r[j];
        x[k] := temp_x[j];
        bcap[k] := temp_bcap[j];
        tran_pointer[k] := temp_tran_pointer[j];
        linetype[k] := temp_linetype[j];
        k := k + 1;
        end
      else if temp_tobus[j] = i then
        begin
        frombus[k] := temp_tobus[j];
        tobus[k] := temp_frombus[j];
        r[k] := temp_r[j];
        x[k] := temp_x[j];
        bcap[k] := temp_bcap[j];
        tran_pointer[k] := temp_tran_pointer[j];
        linetype[k] := temp_linetype[j];
        k := k + 1;
        end;
      end;
    end;

  bound[numbus+1]:=k;
  numline2:=k-1 ;

  { build branch addmittances }

  for i:=1 to numline2 do
    begin
    z.r:=r[i];
    z.i:=x[i];
    recip(y[i],z);
    ys[i].r:=0.0;
    ys[i].i:=bcap[i];
    end;

  if debug then
    for i:=1 to numline2 do writeln(frombus[i]:4,tobus[i]:4,
      y[i].r,y[i].i,ys[i].r,ys[i].i);

quit:

end; { input_lfdata }
{----------------------------------------------------------------------------}
procedure file_sedata;

var
    i,j,busno:integer;
    filename:string[25];

label quit;

begin { file_sedata }
  writeln;
  write('Enter name of state estimator data file :');
  readln(filename);
  writeln;
  linenumber := 0;
  assign(outfile,filename);
  rewrite(outfile);                   iocheck( linenumber);
                                      if ioerr then goto quit;


  { output titles and constants }

  linenumber := linenumber + 1;
  writeln(outfile,title1);            iocheck( linenumber);
                                      if ioerr then goto quit;

  linenumber := linenumber + 1;
  writeln(outfile,title2);            iocheck( linenumber);
                                      if ioerr then goto quit;

  linenumber := linenumber + 1;
  writeln(outfile,numbus:1 );         iocheck( linenumber);
                                      if ioerr then goto quit;

  linenumber := linenumber + 1;
  writeln(outfile,numlines:1 );       iocheck( linenumber);
                                      if ioerr then goto quit;


  { write out line data }

  for i := 1 to numline2 do if frombus[i] < tobus[i] then
    begin
    linenumber := linenumber + 1;
    write(outfile,linetype[i],' ');   iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,frombus[i]:4,' ');  iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,tobus[i]:4,' ');    iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,r[i]:12,' ');       iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,x[i]:12,' ');       iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,bcap[i]:12);        iocheck( linenumber);
                                      if ioerr then goto quit;

    if linetype[i] = 'TRAN' then
      begin
      j := tran_pointer[ i ];
      write(outfile,tapbus[j]:4,' '); iocheck( linenumber);
                                      if ioerr then goto quit;

      writeln(outfile,tapratio[j]:12); iocheck( linenumber);
                                       if ioerr then goto quit;

      end;
    writeln(outfile);                 iocheck( linenumber);
                                      if ioerr then goto quit;

    end;

  { output bus voltage magnitude measurements }

  for i := 1 to numvoltmag do with zvoltmag[i] do
    begin
    linenumber := linenumber + 1;
    write(outfile,'V ');              iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,bus:4,' ');         iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,z:20,' ');          iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,stddev:10);         iocheck( linenumber);
                                      if ioerr then goto quit;

    writeln(outfile);                 iocheck( linenumber);
                                      if ioerr then goto quit;

    end;

  { output bus voltage angle measurements }

  for i := 1 to numvoltang do with zvoltang[i] do
    begin
    linenumber := linenumber + 1;
    write(outfile,'A ');              iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,bus:4,' ');         iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,z:20,' ');          iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,stddev:10);         iocheck( linenumber);
                                      if ioerr then goto quit;

    writeln(outfile);                 iocheck( linenumber);
                                      if ioerr then goto quit;

    end;

  { write bus injection measurements }

  for i := 1 to numinjec do with zinjec[i] do
    begin
    linenumber := linenumber + 1;
    write(outfile,'I ');              iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,bus:4,' ');         iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,z.r:20,' ');        iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,stddev.r:10,' ');   iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,z.i:20,' ');        iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,stddev.i:10);       iocheck( linenumber);
                                      if ioerr then goto quit;

    writeln(outfile);                 iocheck( linenumber);
                                      if ioerr then goto quit;

    end;

  { write branch flow measurements }

  for i := 1 to numflow do with zflow[i] do
    begin
    linenumber := linenumber + 1;
    write(outfile,'F ');              iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,frombus[branch]:4,'  ');  iocheck( linenumber);
                                            if ioerr then goto quit;

    write(outfile,tobus[branch]:4,'  ');    iocheck( linenumber);
                                            if ioerr then goto quit;

    write(outfile,z.r:20,' ');        iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,stddev.r:10,' ');   iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,z.i:20,' ');        iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,stddev.i:10);       iocheck( linenumber);
                                      if ioerr then goto quit;

    writeln(outfile);                 iocheck( linenumber);
                                      if ioerr then goto quit;

    end;

  linenumber := linenumber + 1;
  writeln(outfile,'Q');               iocheck( linenumber);
                                      if ioerr then goto quit;


  close(outfile);                     iocheck( linenumber);
                                      if ioerr then goto quit;

quit:

end; { file_sedata }
{----------------------------------------------------------------------------}
procedure input_meas;

var
    i:integer;
    measch:char;
    filename:string[25];

label quit;

procedure rdvoltmag;
begin { rdvoltmag }
  numvoltmag:=numvoltmag+1;
  nummeaslines:=nummeaslines+1;
  with zvoltmag[numvoltmag] do read(inputfile,bus,stddev);
                                      iocheck( linenumber);
end; { rdvoltmag }

procedure rdvoltang;
begin { rdvoltang }
  numvoltang:=numvoltang+1;
  nummeaslines:=nummeaslines+1;
  with zvoltang[numvoltang] do read(inputfile,bus,stddev);
                                      iocheck( linenumber);
end; { rdvoltang }

procedure rdinjec;
begin { rdinjec }
  numinjec:=numinjec+1;
  nummeaslines:=nummeaslines+1;
  with zinjec[numinjec] do
    read(inputfile,bus,stddev.r,stddev.i);    iocheck( linenumber);
end; { rdinjec }

procedure rdflow;
var
    lastbranch,fbus,tbus:integer;
    notfound:boolean;

label quit;

begin { rdflow }
  numflow:=numflow+1;
  with zflow[numflow] do
    begin
    read(inputfile,fbus,tbus,stddev.r,stddev.i);  iocheck( linenumber);
                                                  if ioerr then goto quit;

    branch:=bound[fbus]-1;
    lastbranch:=bound[fbus+1]-1;
    notfound:=true;
    while (branch<lastbranch) and notfound do
      begin
      branch:=branch+1;
      notfound:=(tobus[branch]<>tbus) ;
      end;
    if notfound then
      begin
      numflow:=numflow-1;
      writeln;
      writeln('ERROR - There is no branch from bus ',fbus:1,' to bus ',tbus:1,',');
      writeln('therefore, measurement ',i:1,' is being ignored.');
      writeln;
      end
    else
      nummeaslines:=nummeaslines+1;
    end;

quit:

end; { rdflow }

begin { input_meas }
  writeln;
  write('Enter name of measurement data file :');
  readln(filename);
  writeln;
  linenumber := 0;
  assign( inputfile, filename );  iocheck( linenumber);
                                  if ioerr then goto quit;

  reset( inputfile );             iocheck( linenumber);
                                  if ioerr then goto quit;


  { skip titles }

  linenumber := linenumber + 1;
  readln(inputfile);            iocheck( linenumber);
                                if ioerr then goto quit;


  linenumber := linenumber + 1;
  readln(inputfile);            iocheck( linenumber);
                                if ioerr then goto quit;


{ read measurement data }

  numvoltmag:=0;
  numvoltang:=0;
  numinjec:=0;
  numflow:=0;
  nummeaslines:=0;

  repeat
    linenumber:=linenumber+1;
    read( inputfile, measch);
    if measch in ['V','A','I','F'] then
      case measch of
      'V' : begin
            rdvoltmag;
            if ioerr then goto quit
            end;
      'A' : begin
            rdvoltang;
            if ioerr then goto quit
            end;
      'I' : begin
            rdinjec;
            if ioerr then goto quit
            end;
      'F' : begin
            rdflow;
            if ioerr then goto quit
            end;
      end
    else if measch<>'Q' then
      begin
      writeln;
      writeln('ERROR - Measure type ''',measch,''' does not exist.');
      writeln;
      goto quit
      end;
    readln( inputfile );              iocheck( linenumber);
                                      if ioerr then goto quit;

  until measch='Q';

  close ( inputfile );

quit:

end; { input_meas }
{----------------------------------------------------------------------------}
procedure bldz;
var
    i,j:integer;
procedure addflow(var z:complex;branch:integer);
var
    fbus,tbus:integer;
    temp1,temp2:complex;
begin { addflow }
  fbus:=frombus[branch];
  tbus:=tobus[branch];
  cmult(temp1,ec[tbus],y[branch]);
  cadd(temp2,y[branch],ys[branch]);
  cmult(temp2,ec[fbus],temp2);
  csub(temp1,temp2,temp1);
  conj(temp1,temp1);
  cmult(temp1,ec[fbus],temp1);
  cadd(z,z,temp1);
end; { addflow }
begin { bldz }
  for i:=1 to numvoltmag do with zvoltmag[i] do z:=ep[bus].m;
  for i:=1 to numvoltang do with zvoltang[i] do z:=ep[bus].a;
  for i:=1 to numflow do with zflow[i] do
    begin
    z:=zero;
    addflow(z,branch);
    end;
  for i:=1 to numinjec do with zinjec[i] do
    begin
    z:=zero;
    for j:=bound[bus] to bound[bus+1]-1 do addflow(z,j);
    end;
end; { bldz }
{ ------------------------------------------------------------------}
begin { scada }
  zero.r:=0.0;
  zero.i:=0.0;
  debug:=false;

  input_lfdata;
         if ioerr then goto quit;

  input_solution;
         if ioerr then goto quit;

  input_meas;
         if ioerr then goto quit;

  bldz;

  file_sedata;
         if ioerr then goto quit;


quit:

end. { scada }
