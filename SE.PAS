{$R-}    {Range checking off}
{$B+}    {Boolean complete evaluation on}
{$S+}    {Stack checking on}
{$I+}    {I/O checking on}
{$N-}    {No numeric coprocessor}
{$M 65500,16384,655360} {Turbo 3 default stack and heap}


program state_estimator(input,output,lst,inputfile);


Uses
  Printer, Crt;

label quit;

const
      maxiter=15;
      maxmagmismatch=0.0001;
      maxangmismatch=0.0001;
      maxbus=25;
      maxbus2=50;
      maxline=40;
      maxline2=80;
      maxtran=10;
      maxmeas=100;
      maxzvmag=25;
      maxzvang=25;
      maxzinjec=25;
      maxzflow=80;
      ioval : integer = 0;
      ioerr : boolean = false;
      degrees_per_radian : real = 57.29577951;

type
        polar   = record
                m,a:real;
                end;

        complex = record
                r,i:real;
                end;

        bus_voltage_record = record
              bus,row:integer;
              stddev,z,zo:real;
              noised:boolean;
              end;

        bus_injection_record = record
              bus,row:integer;
              stddev,z,zo:complex;
              noised:boolean;
              end;

        branch_record = record
             branch,row:integer;
             stddev,z,zo:complex;
             noised:boolean;
             end;

        namet=string[8];
        residual_type=string[10];
        branch_type=string[4];

        arb=array [1..maxbus] of real;
        aib=array [1..maxbus] of integer;
        acb=array [1..maxbus] of complex;
        apb=array [1..maxbus] of polar;
        anb=array [1..maxbus] of namet;

        arl2=array [1..maxline2] of real;
        ail2=array [1..maxline2] of integer;
        acl2=array [1..maxline2] of complex;
        all2=array [1..maxline2] of branch_type;

        art=array [1..maxtran] of real;
        ait=array [1..maxtran] of integer;

        arbvzvm=array [1..maxzvmag ] of bus_voltage_record;
        arbvzva=array [1..maxzvang ] of bus_voltage_record;
        arbizi =array [1..maxzinjec] of bus_injection_record;
        arlzf  =array [1..maxzflow ] of branch_record;

        ary_bus2     =array [1..maxbus2] of real;
        mat_bus2_bus2=array [1..maxbus2] of ary_bus2;
        mat_meas_bus2=array [1..maxmeas] of ary_bus2;
        ary_meas     =array [1..maxmeas] of real;

        arp=array[0..30] of real;

var

    debug:boolean;
    i,numbus,numlines,numline2,numgen,numtran:integer;
    numbus2,nummeas,nummeaslines,numlin,numvoltmag,numvoltang:integer;
    numinjec,numflow,numrealmeas:integer;
    a1:integer;
    baserii:real;
    zero:complex;
    rstyp:residual_type;
    filename:string[25];
    inputfile:text;
    inputchar:char;
    output_device : string[7];
    title1,title2:string[80];
    phi:arp;
    zvoltmag:arbvzvm;
    zvoltang:arbvzva;
    zinjec:arbizi;
    zflow:arlzf;
    ri:ary_meas;
    ec:acb;
    ep:apb;
    bound:aib;
    frombus,tobus:ail2;
    y,ys:acl2;
    htrih:mat_bus2_bus2;
    h    :mat_meas_bus2;
    dv   :ary_bus2;
    dz   :ary_meas;
    r,x,bcap:arl2;
    linetype:all2;
    tran_pointer:ail2;
    tapbus:ait;
    tapratio:art;
{ ------------------------------------------------------------------}
procedure complex_add(var c:complex; a,b:complex);
begin { complex_add }
  c.r := a.r + b.r;
  c.i := a.i + b.i;
end; { complex_add }

procedure complex_subtract(var c:complex; a,b:complex);
begin { complex_subtract }
  c.r := a.r - b.r;
  c.i := a.i - b.i;
end; { complex_subtract }

procedure complex_conjugate(var c:complex; a:complex);
begin { complex_conjugate }
  c.r := a.r;
  c.i := -a.i;
end; { complex_conjugate }

procedure complex_multiply(var c:complex; a,b:complex);
begin { complex_multiply }
  c.r := a.r * b.r - a.i * b.i;
  c.i := a.r * b.i + a.i * b.r;
end; { complex_multiply }

procedure complex_scale(var c:complex; a:real; b:complex);
begin { complex_scale }
  c.r := a * b.r;
  c.i := a * b.i;
end; { complex_scale }

procedure complex_divide(var c:complex; a,b:complex);
var
    bmag:real;
begin { complex_divide }
  bmag :=   b.r * b.r + b.i * b.i ;
  c.r  :=  (a.r * b.r + a.i * b.i) / bmag;
  c.i  :=  (b.r * a.i - a.r * b.i) / bmag;
end; { complex_divide }

procedure branch_flow(var flow:complex; branch:integer);
var
    fbus,tbus:integer;
    line_current,charging_current,volt_diff:complex;
begin  { calculate flow on the branch }
    fbus:=frombus[branch];
    tbus:=  tobus[branch];
    complex_subtract(volt_diff,ec[fbus],ec[tbus]);
    complex_multiply(line_current,volt_diff,y[branch]);
    complex_multiply(charging_current,ec[fbus],ys[branch]);
    complex_add(line_current,charging_current,line_current);
    complex_conjugate(line_current,line_current);
    complex_multiply(flow,ec[fbus],line_current);
end; { branch_flow }

procedure complex_reciprocal(var c:complex; a:complex);
var
    amag:real;
begin { complex_reciprocal }
  amag := a.r * a.r + a.i * a.i;
  c.r  :=   a.r / amag;
  c.i  := - a.i / amag;
end; { complex_reciprocal }

{----------------------------------------------------------------------------}
{ <f> <s>   numeric value input procedure }
procedure numinput( var value:real );

{This routine handles keyboard input of real numbers}

var
   number_string : string[20];
   code, i, remainder : integer;
   input_string : string[20];
   decimal_found : boolean ;

label terminate;

begin

for i:= 1 to 20 do input_string[i] := ' '; decimal_found := false;

readln( input_string );

{ If the string is zero length the user just hit the enter key, set}
{ the result to 0.0 and return }

if length( input_string ) = 0 then
         begin
         number_string := '0.0';
         goto terminate
         end;

i := 0;        { Find first non blank character }
remainder := length( input_string );
repeat
i := i + 1;
remainder := remainder - 1;
until ( input_string[i] <> ' ') or ( remainder = 0 );

{ If the last character in the string is blank, the field was blank }
{ set the string to 0.0 }

if input_string[i] = ' ' then
         begin
         number_string := '0.0';
         goto terminate
         end;

{ If remainder = 0 the user entered only one number }

if remainder = 0 then
         begin
         number_string := input_string + '.0';
         goto terminate
         end;

{ Put leading zero on number, behind minus sign if number is neg }

if input_string[i] = '-' then number_string := '-0'
                         else number_string := '0' + input_string[i]; if
input_string[i] = '.' then decimal_found := true;

{ Copy number to number string array }

repeat
i := i + 1;
if input_string[i] <>' ' then
    begin
    number_string := number_string + input_string[i];
    if input_string[i] = '.' then decimal_found := true
    end;
until i = length( input_string );

{ Check on presence of decimal point, if none add one otherwize } {
append a zero }

if decimal_found then number_string := number_string + '0'
                 else number_string := number_string + '.0';

terminate:

val( number_string, value, code );

end; { End numinput procedure }

{----------------------------------------------------------------------------}
{ <f> <s>   numeric value input procedure, not last number on line}
procedure numinpln( var value:real );

{This routine handles keyboard input of real numbers}

var
   number_string : string[20];
   code, i, remainder : integer;
   input_string : string[20];
   decimal_found : boolean ;
   inputchar : char;

label terminate;

begin

for i:= 1 to 20 do input_string[i] := ' ';
decimal_found := false;

repeat
  read(inputchar);
  until inputchar <> ' ';

i := 1;
input_string[i] := inputchar;
repeat
   read( inputchar );
   if inputchar <>' ' then
         begin
         i := i + 1;
         input_string[i] := inputchar
         end;
   until inputchar = ' ';

i := 1;

{ Put leading zero on number, behind minus sign if number is neg }

if input_string[i] = '-' then number_string := '-0'
                         else number_string := '0' + input_string[i];
if input_string[i] = '.' then decimal_found := true;

{ Copy number to number string array }

repeat
i := i + 1;
if input_string[i] <>' ' then
    begin
    number_string := number_string + input_string[i];
    if input_string[i] = '.' then decimal_found := true
    end;
until input_string[i] = ' ';

{ Check on presence of decimal point, if none add one otherwize } {
append a zero }

if decimal_found then number_string := number_string + '0'
                 else number_string := number_string + '.0';

terminate:

val( number_string, value, code );

end; { End numinpln procedure }

{--------------------------------------------------------------------------}
procedure edit_measurements;
var
    error:integer;
    measch:char;

procedure edit_voltage_magnitude;
var
    i : integer;
    notfound:boolean;
    ztemp:bus_voltage_record;
begin { edit_voltage_magnitude }
  with ztemp do
    begin
    noised:=false;
    read(bus);
    numinpln(zo);
    numinput(stddev);
    notfound := true;
    for i:= 1 to numvoltmag do
      begin
      if zvoltmag[i].bus = bus then
         begin
         zvoltmag[i]:=ztemp;
         notfound := false
         end;
      end;
    end;
    if notfound then
    begin
    writeln;
    writeln('ERROR - no such bus voltage measurement');
    writeln
    end;

end; { edit_voltage_magnitude }

procedure edit_voltage_angle;
var
    i : integer;
    notfound:boolean;
    ztemp:bus_voltage_record;
begin { edit_voltage_angle }
  with ztemp do
    begin
    noised:=false;
    read(bus);
    numinpln(zo);
    numinput(stddev);
    notfound := true;
    for i:= 1 to numvoltang do
      begin
      if zvoltang[i].bus = bus then
          begin
          zvoltang[i]:=ztemp;
          notfound := false
          end;
      end;
    end;
    if notfound then
       begin
       writeln;
       writeln('ERROR - no such bus angle measurement');
       writeln
       end;

end; { edit_voltage_angle }

procedure edit_injection;
var
    i : integer;
    notfound:boolean;
    ztemp:bus_injection_record;
begin { edit_injection }

  with ztemp do
    begin
    noised:=false;
    read(bus);
    numinpln(zo.r);
    numinpln(stddev.r);
    numinpln(zo.i);
    numinput(stddev.i);
    notfound := true;
    for i:= 1 to numinjec do
      begin
      if zinjec[i].bus = bus then
         begin
         zinjec[i]:=ztemp;
         notfound := false
         end;
      end;
  end;
    if notfound then
       begin
       writeln;
       writeln('ERROR - no such bus injection measurement');
       writeln
       end;

end; { edit_injection }

procedure edit_flow;
var
    i,j,fbus,tbus:integer;
    notfound:boolean;
    ztemp:branch_record;
begin { edit_flow }
  with ztemp do
    begin
    noised:=false;
    read(fbus,tbus);
    numinpln(zo.r);
    numinpln(stddev.r);
    numinpln(zo.i);
    numinput(stddev.i);
    zo.r := zo.r/100.0 ;
    zo.i := zo.i/100.0 ;

    i:=0;
    notfound:=true;
    for i := 1 to numflow do
        begin
        with zflow[i] do
           begin
           if (frombus[branch]=fbus) and (tobus[branch]=tbus) then
              begin
              notfound := false;
              j := i
              end;
           end;
        end;

      if notfound then
      writeln('ERROR - invalid branch')
      else
      begin
      zflow[j].noised := ztemp.noised;
      zflow[j].zo.r := ztemp.zo.r;
      zflow[j].zo.i := ztemp.zo.i;
      zflow[j].stddev.r := ztemp.stddev.r;
      zflow[j].stddev.i := ztemp.stddev.i
      end;
   end;
end; { edit_flow }
begin { edit_measurements }
  repeat
  writeln;
  writeln('Enter option type (V,A,I,F or Q), bus number(s),');
  writeln('measurement value(s), sigma(s)');
  writeln;
  writeln('V bus-number per-unit-voltage sigma');
  writeln('A bus-number phaseangle(in radians) sigma');
  writeln('I bus-number MW Psigma MVAR Qsigma');
  writeln('F fbus-number tbus-number MW Psigma MVAR Qsigma');
  writeln('Q to quit');writeln;
  writeln('Enter new measurement data ( or Q to quit) :');

  read(measch);
    if measch in ['V','v','A','a','I','i','F','f'] then
      case measch of
      'V' : edit_voltage_magnitude;
      'v' : edit_voltage_magnitude;
      'A' : edit_voltage_angle;
      'a' : edit_voltage_angle;
      'I' : edit_injection;
      'i' : edit_injection;
      'F' : edit_flow;
      'f' : edit_flow;
      end;

  until (measch='Q') or (measch='q');
  end; { edit_measurements }

{----------------------------------------------------------------------------}

procedure init_measurements;
var
    i,offset:integer;
begin { init_measurements }
  {                                                }
  { order the measurements by the following order: }
  { 1) real injection measurements                 }
  { 2) real flow measurements                      }
  { 3) voltage angle meassurements                 }
  { 4) reactive injection measurements             }
  { 5) reactive flow measurements                  }
  { 6) voltage magnitude measurements              }
  {                                                }
  { note, for the injection and flow measurements, }
  { the variable row points to the row for the     }
  { real measurement.  to get to the row for the   }
  { reactive measurement, you have to add the      }
  { variable numrealmeas to the variable row.      }
  {                                                }

  for i:=1 to numinjec do zinjec[i].row:=i;
  offset:=numinjec;
  for i:=1 to numflow do zflow[i].row:=i+offset;
  offset:=offset+numflow;
  for i:=1 to numvoltang do zvoltang[i].row:=i+offset;
  offset:=offset+numvoltang;
  numrealmeas:=offset;
  offset:=offset+numinjec+numflow;
  for i:=1 to numvoltmag do zvoltmag[i].row:=i+offset;
  nummeas:=offset+numvoltmag;

  { build ri and set z to zo if the measurement has not had noise added }

  for i:=1 to numinjec do with zinjec[i] do
    begin
    ri[row]:=1.0/(stddev.r*stddev.r);
    ri[row+numrealmeas]:=1.0/(stddev.i*stddev.i);
    if not noised then z:=zo;
    end;
  for i:=1 to numflow do with zflow[i] do
    begin
    ri[row]:=1.0/(stddev.r*stddev.r);
    ri[row+numrealmeas]:=1.0/(stddev.i*stddev.i);
    if not noised then z:=zo;
    end;
  for i:=1 to numvoltang do with zvoltang[i] do
    begin
    ri[row]:=1.0/(stddev*stddev);
    if not noised then z:=zo;
    end;
  for i:=1 to numvoltmag do with zvoltmag[i] do
    begin
    ri[row]:=1.0/(stddev*stddev);
    if not noised then z:=zo;
    end;

  { normalize ri }

  baserii:=0;
  for i:=1 to nummeas do baserii:=baserii+ri[i];
  baserii:=nummeas/baserii;
  for i:=1 to nummeas do ri[i]:=ri[i]*baserii;

end; { init_measurements }
{ ------------------------------------------------------------------}
procedure set_voltages_to_flat_start;
var
    i:integer;
begin { set_voltages_to_flat_start }

  { initialize bus voltages }

  for i := 1 to numbus do
    begin
    ep[i].m := 1.0;
    ep[i].a := 0.0;
    ec[i].r := 1.0;
    ec[i].i := 0.0;
    end;

end; { set_voltages_to_flat_start }
{----------------------------------------------------------------------------}
function normal_random_variable:real;
var
    j:integer;
    t,ran1,y:real;
begin { normal_random_variable }
  {                                                      }
  { put a uniform random variable (i.e. 0 - 1) into ran1 }
  {                                                      }
  t:=(a1*32749+3) mod 32749;
  a1:=trunc(t);
  ran1:=abs(t/32749);
  if debug then writeln('UNIFORM RANDOM GENERATED IS ',ran1:1:4);
{ ran1:=random; }
  {                      }
  { convert to normal rv }
  {                      }
  if ran1>=0.5 then
    begin
      j:=0;
      repeat j:=j+1 until (phi[j]>ran1) or (j=30);
      if j=30 then
        y:=4.0
      else
        begin
        j:=j-1;
        y:=j/10.0+(ran1-phi[j])*0.1/(phi[j+1]-phi[j]);
        end;
    end
  else
    begin
    ran1:=1.0-ran1;
    j:=0;
    repeat j:=j+1 until (phi[j]>ran1) or (j=30);
    if j=30 then
      y:=-4.0
    else
      begin
      j:=j-1;
      y:=j/10.0+(ran1-phi[j])*0.1/(phi[j+1]-phi[j]);
      y:=-y;
      end;
    end;
  normal_random_variable := y;
{ writeln(y:15:10,'   ',a1:10); }
end; { normal_random_variable }
{----------------------------------------------------------------------------}
procedure bldphi;
var
    i:integer;
    x,t,d:real;
begin
  for i:=0 to 30 do
    begin
    x:=i/10.0;
    t:=1.0/(1.0+0.2316419*abs(x));
    d:=0.3989423*exp(-x*x/2.0);
    phi[i]:=1.0-d*t*(0.3193815+t*(-0.3565638+t*(1.781478+
    t*(-1.821256+t*1.330274))));
    if debug then writeln('PHI OF ',i/10.0:2:1,' IS ',phi[i]:1:4);
    end;
end;
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

{----------------------------------------------------------------------------}
procedure input_data;

var
    linenumber:integer;

label quit;

procedure input_meas;

var
    i:integer;
    measch:char;
    filename:string[25];

label quit;


procedure read_voltage_magnitude;
begin { read_voltage_magnitude }
  numvoltmag:=numvoltmag+1;
  nummeaslines:=nummeaslines+1;
  with zvoltmag[numvoltmag] do read(inputfile,bus,zo,stddev);
                                               iocheck( linenumber);
end; { read_voltage_magnitude }

procedure read_voltage_angle;
begin { read_voltage_angle }
  numvoltang:=numvoltang+1;
  nummeaslines:=nummeaslines+1;
  with zvoltang[numvoltang] do read(inputfile,bus,zo,stddev);
                                           iocheck( linenumber);
end; { read_voltage_angle }

procedure read_injection;
begin { read_injection }
  numinjec:=numinjec+1;
  nummeaslines:=nummeaslines+1;
  with zinjec[numinjec] do
    read(inputfile,bus,zo.r,stddev.r,zo.i,stddev.i);
                                           iocheck( linenumber);
end; { read_injection }

procedure read_flow;
var
    lastbranch,fbus,tbus:integer;
    notfound:boolean;

label quit;

begin { read_flow }
  numflow:=numflow+1;
  with zflow[numflow] do
    begin
    read(inputfile,fbus,tbus,zo.r,stddev.r,zo.i,stddev.i);
                                           iocheck( linenumber);
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

end; { read_flow }

begin { input_meas }


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
            read_voltage_magnitude;
            if ioerr then goto quit
            end;
      'A' : begin
            read_voltage_angle;
            if ioerr then goto quit
            end;
      'I' : begin
            read_injection;
            if ioerr then goto quit
            end;
      'F' : begin
            read_flow;
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
    readln( inputfile );              iocheck( linenumber );
                                      if ioerr then goto quit;

  until measch='Q';

  { set all noise flags to false }

  for i:=1 to numinjec do zinjec[i].noised:=false;
  for i:=1 to numflow do zflow[i].noised:=false;
  for i:=1 to numvoltang do zvoltang[i].noised:=false;
  for i:=1 to numvoltmag do zvoltmag[i].noised:=false;

quit:

end; { input_meas }

{----------------------------------------------------------------}
procedure input_network;
type
     arl=array [1..maxline] of real;
     ail=array [1..maxline] of integer;
     all=array [1..maxline] of branch_type;
var
    i,j,k:integer;
    temp_frombus,temp_tobus,temp_tran_pointer:ail;
    temp_r,temp_x,temp_bcap,temp_linelimit:arl;
    temp_linetype:all;
    z:complex;

label quit;

begin { input_network }

  { read titles and constants }

  linenumber := linenumber + 1;
  readln( inputfile, title1 );  iocheck( linenumber);
                                if ioerr then goto quit;

  linenumber := linenumber + 1;
  readln( inputfile, title2 );  iocheck( linenumber);
                                if ioerr then goto quit;

  linenumber := linenumber + 1;
  readln( inputfile, numbus );  iocheck( linenumber);
                                if ioerr then goto quit;

  linenumber := linenumber + 1;
  readln( inputfile, numlines );iocheck( linenumber);
                                if ioerr then goto quit;

  { read line data }

  numtran := 0;
  for i := 1 to numlines do
    begin
    linenumber := linenumber + 1;
    read( inputfile, temp_linetype[i] );   iocheck( linenumber);
                                           if ioerr then goto quit;
    read( inputfile, temp_frombus[i] );    iocheck( linenumber);
                                           if ioerr then goto quit;
    read( inputfile, temp_tobus[i] );      iocheck( linenumber);
                                           if ioerr then goto quit;
    read( inputfile, temp_r[i] );          iocheck( linenumber);
                                           if ioerr then goto quit;
    read( inputfile, temp_x[i] );          iocheck( linenumber);
                                           if ioerr then goto quit;
    read( inputfile, temp_bcap[i] );       iocheck( linenumber);
                                           if ioerr then goto quit;
    if temp_linetype[i] = 'TRAN' then
      begin
      numtran := numtran + 1;
      read( inputfile, tapbus[ numtran ] );iocheck( linenumber);
                                           if ioerr then goto quit;
      read( inputfile, tapratio[ numtran ] );iocheck( linenumber);
                                             if ioerr then goto quit;
      temp_tran_pointer[ i ] := numtran
      end;
    readln( inputfile );                   iocheck( linenumber);
                                           if ioerr then goto quit;
    end;

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
  numbus2:=numbus+numbus;

  { build branch addmittances }

  for i:=1 to numline2 do
    begin
    z.r:=r[i];
    z.i:=x[i];
    complex_reciprocal(y[i],z);
    ys[i].r:=0.0;
    ys[i].i:=bcap[i];
    end;

  if debug then
    for i:=1 to numline2 do writeln(frombus[i]:4,tobus[i]:4,
      y[i].r,y[i].i,ys[i].r,ys[i].i);

quit:

end; { input_network }

begin { input_data }
  writeln;
  write('Enter name of state estimator data file :');
  readln(filename);
  writeln;
  linenumber := 0;
  assign( inputfile, filename );  iocheck( linenumber);
                                  if ioerr then goto quit;
  reset( inputfile );             iocheck( linenumber);
                                  if ioerr then goto quit;
  input_network;
         if ioerr then goto quit;
  input_meas;
         if ioerr then goto quit;
  close ( inputfile );

  writeln;
  write('Do you want output on printer? (Y or N) ');
  readln(inputchar); writeln;
  if (inputchar = 'Y') or (inputchar = 'y') then
    output_device := 'printer'
   else
    output_device := 'display';

  set_voltages_to_flat_start;
  rstyp:='          ';

quit:

end; { input_data }
{----------------------------------------------------------------------------}
procedure output_data(var outfile:text);
var
    i,j,busno:integer;
begin { output_data }

  writeln(outfile);
  writeln(outfile,'File: ',filename );
  writeln(outfile);
  writeln(outfile,title1);
  writeln(outfile,title2);
  writeln(outfile);
  writeln(outfile,'Number of Buses = ',numbus:1 );
  writeln(outfile,'Numbar of Lines = ',numlines:1 );
  writeln(outfile,'Number of Transformers = ', numtran:1 );
  writeln(outfile,'Number of Measurements = ',nummeaslines:1 );
  writeln(outfile,'Number of Voltage Magnitude Measurements = ',numvoltmag:1 );
  writeln(outfile,'Number of Voltage Angle Measurements = ',numvoltang:1 );
  writeln(outfile,'Number of Injection Measurements = ',numinjec:1 );
  writeln(outfile,'Number of Flow Measurements = ',numflow:1 );
  writeln(outfile);

  { write out input line data }

  writeln(outfile);
  writeln(outfile,'Branch Data in Per Unit');
  writeln(outfile);
  writeln(outfile,'Branch  From  To    Branch  Branch  Line      Tap   Tap   ');
  writeln(outfile,'Type    Bus   Bus     R       X     Charging  Bus   Ratio ');
  writeln(outfile,'------  ----  ----  ------  ------  --------  ----  ------');
  for i := 1 to numline2 do if frombus[i] < tobus[i] then
    begin
    write(outfile,' ');
    write(outfile,linetype[i],'   ');
    write(outfile,frombus[i]:4,'  ');
    write(outfile,tobus[i]:4,'  ');
    write(outfile,r[i]:6:4,'  ');
    write(outfile,x[i]:6:4,'  ');
    write(outfile,bcap[i]:8:6);
    if linetype[i] = 'TRAN' then
      begin
      j := tran_pointer[ i ];
      write(outfile,'  ');
      write(outfile,tapbus[j]:4,'  ');
      writeln(outfile,tapratio[j]:6:4);
      end;
    writeln(outfile);
    end;

  { write bus voltage magnitude measurements }

  writeln(outfile);
  writeln(outfile,'Bus Voltage Magnitude Measurements in Per Unit');
  writeln(outfile);
  writeln(outfile,'Bus     Voltage    Standard');
  writeln(outfile,'Number  Magnitude  Deviation');
  writeln(outfile,'------  ---------  ---------');
  for i := 1 to numvoltmag do with zvoltmag[i] do
    begin
    write(outfile,bus:6,'  ');
    write(outfile,zo:9:5,'  ');
    write(outfile,stddev:9:5);
    writeln(outfile);
    end;

  { write bus voltage angle measurements }

  writeln(outfile);
  writeln(outfile,'Bus Voltage Angle Measurements in Per Unit (i.e. Radians)');
  writeln(outfile);
  writeln(outfile,'Bus      Voltage   Standard');
  writeln(outfile,'Number   Angle     Deviation');
  writeln(outfile,'------  ---------  ---------');
  for i := 1 to numvoltang do with zvoltang[i] do
    begin
    write(outfile,bus:6,'  ');
    write(outfile,zo:9:5,'  ');
    write(outfile,stddev:9:5);
    writeln(outfile);
    end;

  { write bus injection measurements }

  writeln(outfile);
  writeln(outfile,'Bus Injection Measurements in Per Unit (100 Mva Base)');
  writeln(outfile);
  writeln(outfile,'Bus     Mw         Standard   Mvar       Standard ');
  writeln(outfile,'Number  Injection  Deviation  Injection  Deviation');
  writeln(outfile,'------  ---------  ---------  ---------  ---------');
  for i := 1 to numinjec do with zinjec[i] do
    begin
    write(outfile,bus:6,'  ');
    write(outfile,zo.r:9:5,'  ');
    write(outfile,stddev.r:9:5,'  ');
    write(outfile,zo.i:9:5,'  ');
    write(outfile,stddev.i:9:5);
    writeln(outfile);
    end;

  { write branch flow measurements }

  writeln(outfile);
  writeln(outfile,'Branch Flow Measurements in Per Unit (100 Mva Base)');
  writeln(outfile);
  writeln(outfile,'From  To               Standard              Standard ');
  writeln(outfile,'Bus   Bus    Mw Flow   Deviation  Mvar Flow  Deviation');
  writeln(outfile,'----  ----  ---------  ---------  ---------  ---------');
  for i := 1 to numflow do with zflow[i] do
    begin
    write(outfile,frombus[branch]:4,'  ');
    write(outfile,tobus[branch]:4,'  ');
    write(outfile,zo.r:9:5,'  ');
    write(outfile,stddev.r:9:5,'  ');
    write(outfile,zo.i:9:5,'  ');
    write(outfile,stddev.i:9:5);
    writeln(outfile);
    end;

    writeln(outfile);

end; { output_data }
{----------------------------------------------------------------------------}
procedure output_residuals(var outfile:text);
var
    i:integer;
begin { output_residuals }

  if rstyp='          ' then
    writeln('ERROR - The residuals have not been calculated yet.')
  else
    begin
    writeln(outfile);
    writeln(outfile,'File: ',filename );
    writeln(outfile);
    writeln(outfile,title1);
    writeln(outfile,title2);
    writeln(outfile);
    writeln(outfile,'Number of Voltage Magnitude Measurements = ',numvoltmag:1 );
    writeln(outfile,'Number of Voltage Angle Measurements = ',numvoltang:1 );
    writeln(outfile,'Number of Injection Measurements = ',numinjec:1 );
    writeln(outfile,'Number of Flow Measurements = ',numflow:1 );
    writeln(outfile);

    { write bus voltage magnitude measurements }

    writeln(outfile);
    writeln(outfile,'Bus Voltage Magnitude Measurements');
    writeln(outfile);
    writeln(outfile,'           Voltage Magnitude (in pu)    ');
    writeln(outfile,'        --------------------------------');
    writeln(outfile,'Bus     With out     With     ',rstyp    );
    writeln(outfile,'Number  Noise        Noise    Residual  ');
    writeln(outfile,'------  ---------  ---------  ----------');
    for i := 1 to numvoltmag do with zvoltmag[i] do
      begin
      write(outfile,bus:6,'  ');
      write(outfile,zo:9:5,'  ');
      if noised then
        write(outfile,z:9:5,'  ')
      else
        write(outfile,'   NA      ');
      write(outfile,dz[row]:10:4);
      writeln(outfile);
      end;

    { write bus voltage angle measurements }

    writeln(outfile);
    writeln(outfile,'Bus Voltage Angle Measurements');
    writeln(outfile);
    writeln(outfile,'            Voltage Angle in            ');
    writeln(outfile,'            Per Unit (i.e. Radians)     ');
    writeln(outfile,'        --------------------------------');
    writeln(outfile,'Bus     With out    With      ',rstyp    );
    writeln(outfile,'Number  Noise       Noise     Residual  ');
    writeln(outfile,'------  ---------  ---------  ----------');
    for i := 1 to numvoltang do with zvoltang[i] do
      begin
      write(outfile,bus:6,'  ');
      write(outfile,zo:9:5,'  ');
      if noised then
        write(outfile,z:9:5,'  ')
      else
        write(outfile,'   NA      ');
      write(outfile,dz[row]:10:4);
      writeln(outfile);
      end;

    { write bus injection measurements }

    writeln(outfile);
    writeln(outfile,'Bus Injection Measurements');
    writeln(outfile);
    writeln(outfile,'                  Mw Injection                    Mvar Injection         ');
    writeln(outfile,'        --------------------------------  -------------------------------');
    writeln(outfile,'Bus     With out     With     ',rstyp, '  With out     With     ',rstyp   );
    writeln(outfile,'Number  Noise        Noise    Residual    Noise        Noise    Residual ');
    writeln(outfile,'------  ---------  ---------  ----------  ---------  ---------  ---------');
    for i := 1 to numinjec do with zinjec[i] do
      begin
      write(outfile,bus:6,'  ');
      write(outfile,100*zo.r:9:3,'  ');
      if noised then
        write(outfile,100*z.r:9:3,'  ')
      else
        write(outfile,'   NA      ');
      write(outfile,dz[row]:10:4,'  ');
      write(outfile,100*zo.i:9:3,'  ');
      if noised then
        write(outfile,100*z.i:9:3,'  ')
      else
        write(outfile,'   NA      ');
      write(outfile,dz[row+numrealmeas]:10:4);
      writeln(outfile);
      end;

    { write branch flow measurements }

    writeln(outfile);
    writeln(outfile,'Branch Flow Measurements');
    writeln(outfile);
    writeln(outfile,'                        Mw Flow                          Mvar Flow            ');
    writeln(outfile,'            --------------------------------  --------------------------------');
    writeln(outfile,'From  To    With out     With     ',rstyp, '  With out     With     ',rstyp    );
    writeln(outfile,'Bus   Bus   Noise        Noise    Residual    Noise        Noise    Residual  ');
    writeln(outfile,'----  ----  ---------  ---------  ----------  ---------  ---------  ----------');
    for i := 1 to numflow do with zflow[i] do
      begin
      write(outfile,frombus[branch]:4,'  ');
      write(outfile,tobus[branch]:4,'  ');
      write(outfile,100*zo.r:9:3,'  ');
      if noised then
        write(outfile,100*z.r:9:3,'  ')
      else
        write(outfile,'   NA      ');
      write(outfile,dz[row]:10:4,'  ');
      write(outfile,100*zo.i:9:3,'  ');
      if noised then
        write(outfile,100*z.i:9:3,'  ')
      else
        write(outfile,'   NA      ');
      write(outfile,dz[row+numrealmeas]:10:4);
      writeln(outfile);
      end;
    writeln(outfile);
    end;

end; { output_residuals }
{----------------------------------------------------------------------------}
procedure output_measurements(var outfile:text);
var
    i:integer;
begin { output_measurements }

  writeln(outfile);
  writeln(outfile,'File: ',filename );
  writeln(outfile);
  writeln(outfile,title1);
  writeln(outfile,title2);
  writeln(outfile);
  writeln(outfile,'Number of Voltage Magnitude Measurements = ',numvoltmag:1 );
  writeln(outfile,'Number of Voltage Angle Measurements = ',numvoltang:1 );
  writeln(outfile,'Number of Injection Measurements = ',numinjec:1 );
  writeln(outfile,'Number of Flow Measurements = ',numflow:1 );
  writeln(outfile);

  { write bus voltage magnitude measurements }

  writeln(outfile);
  writeln(outfile,'Bus Voltage Magnitude Measurements');
  writeln(outfile);
  writeln(outfile,'           Voltage Magnitude (in pu)   ');
  writeln(outfile,'        -------------------------------');
  writeln(outfile,'Bus     With out     With     Standard ');
  writeln(outfile,'Number  Noise        Noise    Deviation');
  writeln(outfile,'------  ---------  ---------  ---------');
  for i := 1 to numvoltmag do with zvoltmag[i] do
    begin
    write(outfile,bus:6,'  ');
    write(outfile,zo:9:5,'  ');
    if noised then
      write(outfile,z:9:5,'  ')
    else
      write(outfile,'   NA      ');
    write(outfile,stddev:9:5);
    writeln(outfile);
    end;

  { write bus voltage angle measurements }

  writeln(outfile);
  writeln(outfile,'Bus Voltage Angle Measurements');
  writeln(outfile);
  writeln(outfile,'            Voltage Angle in           ');
  writeln(outfile,'            Per Unit (i.e. Radians)    ');
  writeln(outfile,'        -------------------------------');
  writeln(outfile,'Bus     With out    With      Standard ');
  writeln(outfile,'Number  Noise       Noise     Deviation');
  writeln(outfile,'------  ---------  ---------  ---------');
  for i := 1 to numvoltang do with zvoltang[i] do
    begin
    write(outfile,bus:6,'  ');
    write(outfile,zo:9:5,'  ');
    if noised then
      write(outfile,z:9:5,'  ')
    else
      write(outfile,'   NA      ');
    write(outfile,stddev:9:5);
    writeln(outfile);
    end;

  { write bus injection measurements }

  writeln(outfile);
  writeln(outfile,'Bus Injection Measurements');
  writeln(outfile);
  writeln(outfile,'                 Mw Injection                    Mvar Injection         ');
  writeln(outfile,'        -------------------------------  -------------------------------');
  writeln(outfile,'Bus     With out     With     Standard   With out     With     Standard ');
  writeln(outfile,'Number  Noise        Noise    Deviation  Noise        Noise    Deviation');
  writeln(outfile,'------  ---------  ---------  ---------  ---------  ---------  ---------');
  for i := 1 to numinjec do with zinjec[i] do
    begin
    write(outfile,bus:6,'  ');
    write(outfile,100*zo.r:9:3,'  ');
    if noised then
      write(outfile,100*z.r:9:3,'  ')
    else
      write(outfile,'   NA      ');
    write(outfile,100*stddev.r:9:3,'  ');
    write(outfile,100*zo.i:9:3,'  ');
    if noised then
      write(outfile,100*z.i:9:3,'  ')
    else
      write(outfile,'   NA      ');
    write(outfile,100*stddev.i:9:3);
    writeln(outfile);
    end;

  { write branch flow measurements }

  writeln(outfile);
  writeln(outfile,'Branch Flow Measurements');
  writeln(outfile);
  writeln(outfile,'                        Mw Flow                         Mvar Flow           ');
  writeln(outfile,'            -------------------------------  -------------------------------');
  writeln(outfile,'From  To    With out     With     Standard   With out     With     Standard ');
  writeln(outfile,'Bus   Bus   Noise        Noise    Deviation  Noise        Noise    Deviation');
  writeln(outfile,'----  ----  ---------  ---------  ---------  ---------  ---------  ---------');
  for i := 1 to numflow do with zflow[i] do
    begin
    write(outfile,frombus[branch]:4,'  ');
    write(outfile,tobus[branch]:4,'  ');
    write(outfile,100*zo.r:9:3,'  ');
    if noised then
      write(outfile,100*z.r:9:3,'  ')
    else
      write(outfile,'   NA      ');
    write(outfile,100*stddev.r:9:3,'  ');
    write(outfile,100*zo.i:9:3,'  ');
    if noised then
      write(outfile,100*z.i:9:3,'  ')
    else
      write(outfile,'   NA      ');
    write(outfile,100*stddev.i:9:3);
    writeln(outfile);
    end;

    writeln(outfile);

end; { output_measurements }
{----------------------------------------------------------------------------}
procedure add_measurement_noise;
var
    i:integer;
begin { add_measurement_noise }
  rstyp:='          ';
  for i:=1 to numinjec do with zinjec[i] do
    begin
    z.r:=zo.r+normal_random_variable*stddev.r;
    z.i:=zo.i+normal_random_variable*stddev.i;
    noised:=true;
    end;
  for i:=1 to numflow do with zflow[i] do
    begin
    z.r:=zo.r+normal_random_variable*stddev.r;
    z.i:=zo.i+normal_random_variable*stddev.i;
    noised:=true;
    end;
  for i:=1 to numvoltang do with zvoltang[i] do
    begin
    z:=zo+normal_random_variable*stddev;
    noised:=true;
    end;
  for i:=1 to numvoltmag do with zvoltmag[i] do
    begin
    z:=zo+normal_random_variable*stddev;
    noised:=true;
    end;
end; { add_measurement_noise }
{----------------------------------------------------------------------------}
procedure output_solution(var outfile:text);
var
    i, j, fbus, branch : integer;
    losses:complex;
    mva:real;
    injection:acb;
    flow:acl2;
begin { output_solution }

  {                                           }
  { calcuate the injections, flows and losses }
  {                                           }

  for i:=1 to numbus do injection[i]:=zero;
  for branch:=1 to numline2 do
    begin
    branch_flow(flow[branch],branch);
    fbus := frombus[branch];
    complex_add(injection[fbus],injection[fbus],flow[branch]);
    end;
  losses:=zero;
  for i:=1 to numbus do complex_add(losses,losses,injection[i]);

  {                        }
  { write out the solution }
  {                        }
  writeln(outfile);
  writeln(outfile,'State Estimator Solution:');
  writeln(outfile);
  writeln(outfile,'file: ',filename );
  writeln(outfile);
  writeln(outfile,title1);
  writeln(outfile,title2);
  writeln(outfile);
  writeln(outfile,'From Volt.  Volt.   Mw       Mvar    To    Mw      Mvar    Mva   ');
  writeln(outfile,'Bus  Mag.   Angle   Injec.   Injec.  Bus   Flow    Flow    Flow  ');
  writeln(outfile,'---- ------ ------ -------- -------- ---- ------- ------- -------');
  fbus := 0;
  for branch := 1 to numline2 do
    begin
    if fbus <> frombus[branch] then
      begin
      fbus := frombus[branch];
      writeln(outfile);
      write(outfile,fbus:4,' ');
      write(outfile,ep[fbus].m:6:4,' ');
      write(outfile,degrees_per_radian*ep[fbus].a:6:3,' ');
      write(outfile,100.0*injection[fbus].r:7:2,' ');
      writeln(outfile,100.0*injection[fbus].i:7:2);
      end;
    {                                 }
    { write out the tbus and the flow }
    {                                 }
    with flow[branch] do
      begin
      mva := sqrt(r*r+i*i);
      for j := 1 to 37 do write(outfile,' ');
      write(outfile,tobus[branch]:4,' ');
      write(outfile,100.0*r:7:2,' ');
      write(outfile,100.0*i:7:2,' ');
      writeln(outfile,100.0*mva:7:2);
      end;
    end;

  writeln(outfile);
  writeln(outfile);
  writeln(outfile, 'Mw losses   = ',100.0*losses.r:7:2 );
  writeln(outfile, 'Mvar Losses = ',100.0*losses.i:7:2 );

  writeln(outfile);

end;  { output_solution }
{----------------------------------------------------------------------------}
procedure build_h;
var
    i,j:integer;
procedure calculate_flow_derivative(row,branch:integer);
var
    fbus,tbus:integer;
    temp1,temp2:complex;
begin { calculate_flow_derivative }
   fbus:=frombus[branch];
   tbus:=tobus[branch];
   complex_multiply(temp1,ec[tbus],y[branch]);
   complex_conjugate(temp1,temp1);
   complex_multiply(temp1,ec[fbus],temp1);
   complex_add(temp2,ys[branch],y[branch]);
   complex_conjugate(temp2,temp2);
   complex_scale(temp2,2*ep[fbus].m,temp2);
   h[row,fbus]:=h[row,fbus]+temp1.i;
   h[row,tbus]:=-temp1.i;
   h[row,fbus+numbus]:=h[row,fbus+numbus]+temp2.r-temp1.r/ep[fbus].m;
   h[row,tbus+numbus]:=-temp1.r/ep[tbus].m;
   row:=row+numrealmeas;
   h[row,fbus]:=h[row,fbus]-temp1.r;
   h[row,tbus]:=temp1.r;
   h[row,fbus+numbus]:=h[row,fbus+numbus]+temp2.i-temp1.i/ep[fbus].m;
   h[row,tbus+numbus]:=-temp1.i/ep[tbus].m;
end; { calculate_flow_derivative }

begin { build_h }
  for i:=1 to nummeas do for j:=1 to numbus2 do h[i,j]:=0.0;
  for i:=1 to numvoltmag do with zvoltmag[i] do h[row,bus+numbus]:=1.0;
  for i:=1 to numvoltang do with zvoltang[i] do h[row,bus]:=1.0;
  for i:=1 to numflow do with zflow[i] do calculate_flow_derivative(row,branch);
  for i:=1 to numinjec do with zinjec[i] do
    for j:=bound[bus] to bound[bus+1]-1 do calculate_flow_derivative(row,j);
end; { build_h }
{ ------------------------------------------------------------------}
procedure build_delta_z;
var
    i,j:integer;
    flow:complex;
begin { build_delta_z }
  for i:=1 to numvoltmag do with zvoltmag[i] do dz[row]:=z-ep[bus].m;
  for i:=1 to numvoltang do with zvoltang[i] do dz[row]:=z-ep[bus].a;
  for i:=1 to numflow do with zflow[i] do
    begin
    dz[row]:=z.r;
    dz[row+numrealmeas]:=z.i;
    branch_flow(flow,branch);
    dz[row]:=dz[row]-flow.r;
    dz[row+numrealmeas]:=dz[row+numrealmeas]-flow.i;
    end;
  for i:=1 to numinjec do with zinjec[i] do
    begin
    dz[row]:=z.r;
    dz[row+numrealmeas]:=z.i;
    for j:=bound[bus] to bound[bus+1]-1 do
      begin
      branch_flow(flow,j);
      dz[row]:=dz[row]-flow.r;
      dz[row+numrealmeas]:=dz[row+numrealmeas]-flow.i;
      end;
    end;
end; { build_delta_z }
{ ------------------------------------------------------------------}
procedure factor_gain_matrix;
var
   i,j,k:integer;
   de,ode:real;
begin { factor_gain_matrix }
  for i:=1 to numbus2 do
    begin
    de:=htrih[i,i];
    if abs(de)<1.0e-7 then writeln('ZERO ON ROW ',i:1);
    de:=1.0/de;
    htrih[i,i]:=de;
    for j:=i+1 to numbus2 do htrih[i,j]:=htrih[i,j]*de;
    for j:=i+1 to numbus2 do
      begin
      ode:=htrih[j,i];
      for k:=i+1 to numbus2 do htrih[j,k]:=htrih[j,k]-htrih[i,k]*ode;
      end;
    end;
end; { factor_gain_matrix }
{ ------------------------------------------------------------------}
procedure solve_for_voltage_correction;
var
    i,j:integer;
    ode:real;
begin { solve_for_voltage_correction }
  for i:=1 to numbus2 do
    begin
    ode:=dv[i]*htrih[i,i];
    dv[i]:=ode;
    for j:=i+1 to numbus2 do dv[j]:=dv[j]-htrih[j,i]*ode;
    end;
  for i:=numbus2 downto 1 do
    for j:=i+1 to numbus2 do dv[i]:=dv[i]-dv[j]*htrih[i,j];
end; { solve_for_voltage_correction }
{ ------------------------------------------------------------------}
procedure build_h_transpose_r_inverse_h;
var
    i,j,k:integer;
    sum:real;
begin { build_h_transpose_r_inverse_h }
  for i:=1 to numbus2 do
    for j:=1 to numbus2 do
      begin
      sum:=0.0;
      for k:=1 to nummeas do sum:=sum+h[k,i]*ri[k]*h[k,j];
      htrih[i,j]:=sum;
      end;
end; { build_h_transpose_r_inverse_h }
{ ------------------------------------------------------------------}
procedure build_h_transpose_r_inverse_delta_z;
var
    i,j:integer;
    sum:real;
begin { build_h_transpose_r_inverse_delta_z }
  for i:=1 to numbus2 do
    begin
    sum:=0.0;
    for j:=1 to nummeas do sum:=sum+h[j,i]*ri[j]*dz[j];
    dv[i]:=sum;
    end;
end; { build_h_transpose_r_inverse_delta_z }
{----------------------------------------------------------------------------}
procedure perform_solution;
var
    i,j,k,iteration:integer;
    converged:boolean;
    sswr:real;
{----------------------------------------------------------------------------}
procedure build_sum_of_square_of_weighted_residuals;
var
    i:integer;
begin { build_sum_of_square_of_weighted_residuals }
  sswr:=0.0;
  for i:=1 to nummeas do sswr:=sswr+dz[i]*dz[i]*ri[i];
  sswr:=sswr/baserii;
end; { build_sum_of_square_of_weighted_residuals }
{----------------------------------------------------------------------------}
procedure update_voltage_vector;
var
    j,maxmagbus,maxangbus:integer;
    maxmag,maxang,deltamagnitude,deltaangle:real;
begin { update_voltage_vector }
  maxmagbus:=0;
  maxangbus:=0;
  maxmag:=0.0;
  maxang:=0.0;
  for j:=1 to numbus do with ep[j],ec[j] do
    begin
    deltaangle:=dv[j];
    deltamagnitude:=dv[j+numbus];
    if abs(deltaangle)>=abs(maxang) then
      begin
      maxang:=deltaangle;
      maxangbus:=j;
      end;
    if abs(deltamagnitude)>=abs(maxmag) then
      begin
      maxmag:=deltamagnitude;
      maxmagbus:=j;
      end;
    a:=a+deltaangle;
    m:=m+deltamagnitude;
    r:=m*cos(a);
    i:=m*sin(a);
    end;
    converged:=(abs(maxang)<maxangmismatch) and (abs(maxmag)<maxmagmismatch);
    writeln;
    writeln('Maximum angle mismatch is ',maxang:1:5,' at bus ',maxangbus:1);
    writeln('Maximum magnitude mismatch is ',maxmag:1:5,' at bus ',maxmagbus:1);
    writeln;
end; { update_voltage_vector }
{----------------------------------------------------------------------------}
begin { perform_solution }
  rstyp:='          ';
  set_voltages_to_flat_start;
  writeln('Building R inverse.');
  init_measurements;
  if debug then for i:=1 to nummeas do writeln(ri[i]:10:5);
  iteration:=0;
  repeat
    iteration:=iteration+1;
    writeln;
    writeln('***********************************************************');
    writeln;
    writeln('                   ITERATION ',iteration:1);
    writeln;
    writeln('Building H matrix.');
    build_h;
    if debug then for i:=1 to nummeas do
      begin
      for j:=1 to numbus2 do write(h[i,j]:10:5,' ');
      writeln;
      end;
    writeln('Building H transpose R inverse H.');
    build_h_transpose_r_inverse_h;
    if debug then for i:=1 to numbus2 do
      begin
      for j:=1 to numbus2 do write(htrih[i,j]:10:5,' ');
      writeln;
      end;
    writeln('Building delta Z.');
    build_delta_z;
    if debug then for i:=1 to nummeas do writeln(dz[i]:10:5);
    writeln('Calculating the residual J.');
    build_sum_of_square_of_weighted_residuals;
    writeln('The residual J is ',sswr:8);
    writeln('Building H transpose R inverse delta Z.');
    build_h_transpose_r_inverse_delta_z;
    if debug then for i:=1 to numbus2 do writeln(dv[i]:10:5);
    writeln('Calculating and storing the table of factors.');
    factor_gain_matrix;
    if debug then for i:=1 to numbus2 do
      begin
      for j:=1 to numbus2 do write(htrih[i,j]:10:5,' ');
      writeln;
      end;
    writeln('Using the table of factors to calculate delta V.');
    solve_for_voltage_correction;
    if debug then for i:=1 to numbus2 do writeln(dv[i]:10:5);
    writeln('Updating the bus voltages.');
    update_voltage_vector;
    if debug then
      begin
      writeln;
      writeln('NEW BUS VOLTAGES:');
      writeln;
      writeln('BUS  MAGNITUDE    ANGLE   ');
      writeln('---- ---------- ----------');
      for j:=1 to numbus do with ep[j] do
        writeln(j:4,' ',m:10:5,' ',a*degrees_per_radian:10:5);
      writeln;
    end;
  until converged or (iteration>=maxiter);
  writeln('Building delta Z.');
  build_delta_z;
  if debug then for i:=1 to nummeas do writeln(dz[i]:10:5);
  writeln('Calculating the residual J.');
  build_sum_of_square_of_weighted_residuals;
  writeln('The final value of the residual J is ',sswr:8);
end; { perform_solution }
{----------------------------------------------------------------------------}
procedure build_residual;
var
    i:integer;
    srbaseri:real;
begin
  writeln('Building delta Z.');
  build_delta_z;
  if debug then for i:=1 to nummeas do writeln(dz[i]:20:10);
  srbaseri:=1.0/sqrt(baserii);
  for i:=1 to nummeas do dz[i]:=sqrt(ri[i])*dz[i]*srbaseri;
end;
{----------------------------------------------------------------------------}
procedure build_di;
var
    i,j:integer;
    d:real;
begin
  for i:=1 to nummeas do
    begin
    dv:=h[i];
    solve_for_voltage_correction;
    d:=1.0/ri[i];
    for j:=1 to numbus2 do d:=d-h[i,j]*dv[j];
    ri[i]:=1.0/abs(d);
    end;
end;
{----------------------------------------------------------------------------}
procedure calculate_normalized_residuals;
  var
      i,j:integer;
begin
  rstyp:='Normalized';
  writeln('Building R inverse.');
  init_measurements;
  if debug then for i:=1 to nummeas do writeln(ri[i]:20:10);
  writeln('Building H matrix.');
  build_h;
  if debug then for i:=1 to nummeas do
    begin
    for j:=1 to numbus2 do write(h[i,j]:10:5,' ');
    writeln;
    end;
  writeln('Building H transpose R inverse H.');
  build_h_transpose_r_inverse_h;
  if debug then for i:=1 to numbus2 do
    begin
    for j:=1 to numbus2 do write(htrih[i,j]:10:5,' ');
    writeln;
    end;
  writeln('Calculating and storing the table of factors.');
  factor_gain_matrix;
  if debug then for i:=1 to numbus2 do
    begin
    for j:=1 to numbus2 do write(htrih[i,j]:10:5,' ');
    writeln;
    end;
  writeln('Using the table of factors, H and R inverse to calcuate D inverse.');
  build_di;
  if debug then for i:=1 to nummeas do writeln(ri[i]:20:10);
  build_residual;
end;
{----------------------------------------------------------------------------}
procedure calculate_weighted_residuals;
begin
  rstyp:='Weighted  ';
  writeln('Building R inverse.');
  init_measurements;
  if debug then for i:=1 to nummeas do writeln(ri[i]:10:5);
  build_residual;
end;
{----------------------------------------------------------------------------}
begin { state_estimator }
  debug:=false;
  zero.r:=0.0;
  zero.i:=0.0;
  a1:=29990;
  bldphi;
  i:=1;
  while i<>11 do
    begin
    if i in [1..10] then
      case i of
       1 : begin
           input_data;
           if ioerr then goto quit;
           end;
       2 : begin
           if ( output_device = 'printer') then output_data(lst);
           if ( output_device = 'display') then output_data(output);
           end;
       3 : edit_measurements;
       4 : add_measurement_noise;
       5 : begin
           if ( output_device = 'printer') then output_measurements(lst);
           if ( output_device = 'display') then output_measurements(output);
           end;
       6 : perform_solution;
       7 : begin
           if ( output_device = 'printer') then output_solution(lst);
           if ( output_device = 'display') then output_solution(output);
           end;
       8 : calculate_weighted_residuals;
       9 : calculate_normalized_residuals;
      10 : begin
           if ( output_device = 'printer') then output_residuals(lst);
           if ( output_device = 'display') then output_residuals(output);
           end;
      end;
    writeln;
    writeln('Menu of options:');
    writeln;
    writeln(' 1 - Read in a new input data file');
    writeln(' 2 - Print input data');
    writeln(' 3 - Edit measurement data');
    writeln(' 4 - Add noise to measurements');
    writeln(' 5 - Print measurement data');
    writeln(' 6 - Run State Estimator');
    writeln(' 7 - Print solution');
    writeln(' 8 - Calculate the weighted residuals');
    writeln(' 9 - Calculate the normalized residuals');
    writeln('10 - Print the residuals');
    writeln('11 - Quit');
    writeln;
    write('Enter option >');
    readln(i);
    if ioresult<>0 then i:=0;
    writeln;
  end;

quit:

end. { state_estimator }
{ ------------------------------------------------------------------}
