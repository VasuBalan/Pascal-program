{$R-}    {Range checking off}
{$B+}    {Boolean complete evaluation on}
{$S+}    {Stack checking on}
{$I+}    {I/O checking on}
{$N-}    {No numeric coprocessor}
{$M 65500,16384,655360} {Turbo 3 default stack and heap}

program loadflow;

{  newton and gauss load flow for use with power generation and control }
{           allen j. wood & bruce f. wollenberg                         }


Uses
  Crt,
  Printer;

const

        maxiter_newton = 10;
        maxiter_gauss = 75;
        maxbus = 25;
        maxline = 80;
        maxgen = 20;
        maxtran = 10;
        max_mismatch_newton = 0.001;
        max_volterror_gauss = 0.0001;
        ioval : integer = 0;
        ioerr : boolean = false;
        dpr : real = 57.29577951;

type
        bustype_label = ( load, gen_reg, gen_highvar, gen_lowvar, swing );
        busnametype = string[8];
        lntype = string[4];
        complex = record
                  r,i:real;
                  end;
        polar = record
                m,a:real;
                end;

        bustable_real = array [1..maxbus] of real;
        bustable_bustype = array [1..maxbus] of bustype_label;
        bustable_string = array [1..maxbus] of string[8];
        bustable_integer = array [1..maxbus] of integer;
        bustable_complex = array [1..maxbus] of complex;
        bustable_polar = array [1..maxbus] of polar;
        bustable_square_real = array [1..maxbus] of bustable_real;
        bustable_square_complex = array [1..maxbus] of bustable_complex;
        gentable_real = array [1..maxgen] of real;
        gentable_integer = array [1..maxgen] of integer;
        linetable_real = array [1..maxline] of real;
        linetable_integer = array [1..maxline] of integer;
        linetable_lntype = array [1..maxline] of lntype;
        trantable_real = array [1..maxtran] of real;
        trantable_integer = array [1..maxtran] of integer;
var

        i,iter,
        linenumber,
        numbuses,
        numlines,
        numlines_dbl,
        numgen,
        numtran,
        swingbus
                   : integer;

        no_var_limiting : boolean;

        zero : complex;

        filename : string[ 25 ];

        inputfile,outfile : text;
        inputchar : char;
        output_device : string[7];

        title1, title2 : string[80];

        ec,cn : bustable_complex;

        ep : bustable_polar;

        dele,delang,
        delp,delq,
        pload,qload,
        p_sched_inj, q_sched_inj,
        p_net_inj, q_net_inj,
        volt_low_limit,
        volt_high_limit
                         : bustable_real;

        bustype : bustable_bustype;

        busname : bustable_string;

        buspointer : bustable_integer;

        dpdt,dpde,dqdt,dqde : bustable_square_real;

        y : bustable_square_complex;

        pgen,qgen,
        qmax, qmin,
        vsched
            : gentable_real;

        genbusno : gentable_integer;

        frombus, tobus,
        tran_pointer
            : linetable_integer;

        r,x,bcap,
        linelimit,pflow,qflow
            : linetable_real;

        linetype : linetable_lntype;

        tapbus, nontapbus : trantable_integer;

        tapratio : trantable_real;

label quit;

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
procedure cmag( var c:real; a:complex );
begin
    c := sqrt( a.r * a.r  +  a.i * a.i );
end;
procedure cart_to_polar(var c:polar; a:complex);
begin
  c.m := sqrt(a.r * a.r + a.i * a.i);
  c.a := arctan(a.i / a.r);
end; { cart_to_polar }
procedure polar_to_cart(var c:complex; a:polar);
begin
  c.r := a.m * cos(a.a);
  c.i := a.m * sin(a.a);
end; { polar_to_cart }

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
procedure file_solution;

var
    i,j:integer;
    filename:string[25];

label quit;

begin { file_solution }
  writeln;
  write('Enter name of solution data file :');
  readln(filename);
  writeln;
  linenumber := 0;
  assign( outfile, filename );        iocheck( linenumber);
                                      if ioerr then goto quit;

  rewrite( outfile );                 iocheck( linenumber);
                                      if ioerr then goto quit;

  { write titles }

  linenumber := linenumber + 1;
  writeln(outfile,title1);            iocheck( linenumber);
                                      if ioerr then goto quit;

  linenumber := linenumber + 1;
  writeln(outfile,title2);            iocheck( linenumber);
                                      if ioerr then goto quit;

  { write bus solution data }

  for j:=1 to numbuses do with ep[j] do
    begin
    write(outfile,j:4,' ');           iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,m:20,' ');          iocheck( linenumber);
                                      if ioerr then goto quit;

    write(outfile,a:20,' ');          iocheck( linenumber);
                                      if ioerr then goto quit;

    writeln(outfile);                 iocheck( linenumber);
                                      if ioerr then goto quit;

    end;

  close ( outfile );

quit:

end; { file_solution }
{----------------------------------------------------------------------------}
procedure sumoffdia(var soffdia:complex; fbus:integer);
var
    
    { sum the to bus voltage times the branch addmittance for }
    { each branch connectted to the from bus called fbus. the }
    { result is stored in soffdia.                            }
                                                             
    tbus:integer;
    yline,offdia:complex;
begin { sumoffdia }
  soffdia.r := 0.0;
  soffdia.i := 0.0;
  for tbus := 1 to numbuses do if fbus <> tbus then
    begin
    yline := y[fbus,tbus];
    if (yline.r <> 0) or (yline.i <> 0) then
      begin
      cmult(offdia,ec[tbus],yline);
      cadd(soffdia,soffdia,offdia);
      end;
    end;
end; { sumoffdia }
{----------------------------------------------------------------------------}
procedure datainput;

var i,j,k,busno : integer;
    temp_frombus, temp_tobus, temp_tran_pointer : linetable_integer;
    temp_r, temp_x, temp_bcap, temp_linelimit : linetable_real;
    temp_linetype : linetable_lntype;
    z,gline,bline:real;

label quit;

begin
        linenumber := 0;
        writeln;
        write ( ' Enter name of input data file :' );
        readln( filename );
        writeln;
        assign( inputfile, filename );      iocheck( linenumber);
                                            if ioerr then goto quit;

        reset( inputfile );      iocheck( linenumber);
                                 if ioerr then goto quit;
                               


{ read titles and constants }

linenumber := 1;
readln( inputfile, title1 );      iocheck( linenumber);
                                  if ioerr then goto quit;

linenumber := linenumber + 1;
readln( inputfile, title2 );      iocheck( linenumber);
                                  if ioerr then goto quit;

linenumber := linenumber + 1;
readln( inputfile, numbuses );    iocheck( linenumber);
                                  if ioerr then goto quit;

linenumber := linenumber + 1;
readln( inputfile, numgen   );    iocheck( linenumber);
                                  if ioerr then goto quit;

linenumber := linenumber + 1;
readln( inputfile, numlines );    iocheck( linenumber);
                                  if ioerr then goto quit;

linenumber := linenumber + 1;
readln( inputfile, swingbus  );   iocheck( linenumber);
                                  if ioerr then goto quit;

{ read bus data }

    for i := 1 to numbuses do
        begin
        linenumber := linenumber + 1;
        read( inputfile, busno );                  iocheck( linenumber);
                                                   if ioerr then goto quit;

        repeat
        read( inputfile, inputchar );              iocheck( linenumber);
                                                   if ioerr then goto quit;

        until inputchar <> ' ';

        busname[busno] := inputchar;
        repeat
        read( inputfile, inputchar );              iocheck( linenumber);
                                                   if ioerr then goto quit;


        if inputchar <>' ' then busname[busno] := busname[busno] + inputchar;
        until inputchar = ' ';

        read( inputfile, pload[busno] );           iocheck( linenumber);
                                                   if ioerr then goto quit;

        read( inputfile, qload[busno] );           iocheck( linenumber);
                                                   if ioerr then goto quit;

        read( inputfile, volt_low_limit[busno] );  iocheck( linenumber);
                                                   if ioerr then goto quit;

        readln( inputfile, volt_high_limit[busno] ); iocheck( linenumber);
                                                     if ioerr then goto quit;

        end;

{ read generator data }

    for i := 1 to numgen do
    begin
        linenumber := linenumber + 1;
        read( inputfile, genbusno[i] );            iocheck( linenumber);
                                                   if ioerr then goto quit;
                                                   
        read( inputfile, pgen[i] );                iocheck( linenumber);
                                                   if ioerr then goto quit;
                                                   
        read( inputfile, vsched[i] );              iocheck( linenumber);
                                                   if ioerr then goto quit;
                                                   
        read( inputfile, qmax[i] );                 iocheck( linenumber);
                                                    if ioerr then goto quit;

        readln( inputfile, qmin[i] );               iocheck( linenumber);
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
                                                       
        read( inputfile, temp_linelimit[i] );      iocheck( linenumber);
                                                   if ioerr then goto quit;
                                                       
        read( inputfile, inputchar, temp_linetype[i] ); iocheck( linenumber);
                                                   if ioerr then goto quit;

        if temp_linetype[i] = 'TRAN' then
            begin
                numtran := numtran + 1;
                read( inputfile, tapbus[ numtran ] ); iocheck( linenumber);
                                                   if ioerr then goto quit;
                                                     
                read( inputfile, nontapbus[ numtran ] ); iocheck( linenumber);
                                                   if ioerr then goto quit;
                                                     
                readln( inputfile, tapratio[ numtran ] ); iocheck( linenumber);
                                                   if ioerr then goto quit;
                                                     
                temp_tran_pointer[ i ] := numtran
            end
        else
            readln( inputfile );
    end;

close ( inputfile );

  writeln;
  write('Do you want output on printer? (Y or N) ');
  readln(inputchar); writeln;
  if (inputchar = 'Y') or (inputchar = 'y') then
    output_device := 'printer'
   else
    output_device := 'display';



{ build bus lists }

for i := 1 to numbuses do
      begin
      p_sched_inj[i] := -pload[i];
      q_sched_inj[i] := -qload[i];
      ep[i].m := 1.0;
      ep[i].a := 0.0;
      ec[i].r := 1.0;
      ec[i].i := 0.0;
      bustype[i] :=  load ;
      end;

for i := 1 to numgen do
      begin
      busno := genbusno[i];
      p_sched_inj[busno] := p_sched_inj[busno] + pgen[i];
      bustype[busno] :=  gen_reg  ;
      ep[busno].m := vsched[i];
      ec[busno].r := vsched[i];
      end;

bustype[ swingbus ] :=  swing ;

{
for i := 1 to numbuses do writeln( i, '  ',p_sched_inj[i]:11:4,'  ',
  q_sched_inj[i]:11:4,'  ',ep[i].m:11:4,'  ',ep[i].a:11:4, pload[i]:11:4,
  qload[i]:11:4);
}

{ build double order line tables }

k := 1;

for i := 1 to numbuses do
    begin
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
            linelimit[k] := temp_linelimit[j];
            linetype[k] := temp_linetype[j];
            if buspointer[i] <> 0 then buspointer[i] := k;
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
            linelimit[k] := temp_linelimit[j];
            linetype[k] := temp_linetype[j];
            if buspointer[i] <> 0 then buspointer[i] := k;
            k := k + 1;
            end;
        end;
    end;

numlines_dbl := k - 1 ;

{ build y matrix }

    for i := 1 to maxbus do
            begin
                for j := 1 to maxbus do
                begin
                    y[i,j].r := 0.0;
                    y[i,j].i := 0.0;
                end;
            end;

for k := 1 to numlines_dbl do if tobus[k] > frombus[k] then
      begin
      z := r[k] * r[k]  +  x[k] * x[k];
      gline := r[k] / z;
      bline := -x[k] / z;
      i := frombus[k];
      j := tobus[k];
      y[i,j].r := y[i,j].r - gline;
      y[i,j].i := y[i,j].i - bline;
      y[j,i].r := y[j,i].r - gline;
      y[j,i].i := y[j,i].i - bline;
      y[i,i].r := y[i,i].r + gline;
      y[i,i].i := y[i,i].i + bline + bcap[k];
      y[j,j].r := y[j,j].r + gline;
      y[j,j].i := y[j,j].i + bline + bcap[k];
      end;

quit:

end;   { end of data input }

{----------------------------------------------------------------------------}
procedure check_gen_vars;

var
    busno : integer;

begin

no_var_limiting := true;

for i := 1 to numgen do
    begin
    busno := genbusno[i];
    if bustype[busno] <> swing then
        begin
        qgen[i] := q_net_inj[busno] + qload[busno];
        if qgen[i] > qmax[i] then
            begin
            q_sched_inj[busno] := qmax[i] - qload[busno];
            if bustype[busno] <> gen_highvar then 
                begin
                no_var_limiting := false;
                writeln( ' Gen ',i,' at max var limit');
                bustype[busno] := gen_highvar;
                end;
            end
        else if qgen[i] < qmin[i] then
            begin
            q_sched_inj[busno] := qmin[i] - qload[busno];
            if bustype[busno] <> gen_lowvar then 
                begin
                no_var_limiting := false;
                writeln( ' Gen ',i,' at min var limit');
                bustype[busno] := gen_lowvar;
                end;
            end
        else if ( ( qgen[i] >= qmin[i] ) and ( qgen[i] <= qmax[i] ) ) then
            begin
            bustype[busno] := gen_reg;
            end;
        end;
    end;

end;
{----------------------------------------------------------------------------}
procedure calc_net_power;

var i,j : integer;

  { calculate the net power at all buses }
begin

for i := 1 to numbuses do
begin
    cn[i].r := 0.0;
    cn[i].i := 0.0;
    for j := 1 to numbuses do
    begin
    if i <> j then
        begin
        if ( ( abs( y[i,j].r ) <> 0.0 ) or ( abs( y[i,j].i ) <> 0.0)  ) then
            begin
            cn[i].r := cn[i].r + ec[j].r * y[i,j].r - ec[j].i * y[i,j].i;
            cn[i].i := cn[i].i + ec[j].r * y[i,j].i + ec[j].i * y[i,j].r;
            end;
        end
    else if i=j then
            begin
            cn[i].r := cn[i].r + ec[i].r * y[i,i].r - ec[i].i * y[i,i].i;
            cn[i].i := cn[i].i + ec[i].r * y[i,i].i + ec[i].i * y[i,i].r;
            end;
    end;
    p_net_inj[i] := ec[i].r * cn[i].r + ec[i].i * cn[i].i;
    q_net_inj[i] := ec[i].i * cn[i].r - ec[i].r * cn[i].i;
end;

end;
{----------------------------------------------------------------------------}
procedure newton_solution;

{ solves the load flow by newton raphson solution method }

label skip;

var ak, bk,
    p_max_mismatch, q_max_mismatch ,
    em2,
    temp_dpdt, temp_dpde, temp_dqdt, temp_dqde,
    temp_delp, temp_delq,
    detd, d11, d12, d21, d22
    : real;

    i,j,k : integer;

begin

iter := 0;

repeat

iter := iter + 1;
p_max_mismatch := 0.0;
q_max_mismatch := 0.0;

{ build jacobian matrix, calculate error vectors dele and delq }

for i := 1 to numbuses do
begin

cn[i].r := 0.0;
cn[i].i := 0.0;
delp[i] := 0.0;
delq[i] := 0.0;
dele[i] := 0.0;
delang[i] := 0.0;

for j := 1 to numbuses do
    begin

    dpdt[i,j] := 0.0;
    dpde[i,j] := 0.0;
    dqdt[i,j] := 0.0;
    dqde[i,j] := 0.0;

    if i <> j then
        begin
        
        if ( ( abs( y[i,j].r ) <> 0.0 ) or ( abs( y[i,j].i ) <> 0.0)  ) then
            begin

            ak := ec[j].r * y[i,j].r - ec[j].i * y[i,j].i;
            bk := ec[j].r * y[i,j].i + ec[j].i * y[i,j].r;

            cn[i].r := cn[i].r + ak;
            cn[i].i := cn[i].i + bk;

            case bustype[i] of
                 load, gen_highvar, gen_lowvar  :
                    begin
                    case bustype[j] of
                         load, gen_highvar, gen_lowvar  :
                            begin
                            dpdt[i,j] := ak * ec[i].i - bk * ec[i].r;
                            dpde[i,j] := ak * ec[i].r + bk * ec[i].i;
                            dqdt[i,j] := -(ak * ec[i].r + bk * ec[i].i);
                            dqde[i,j] := ak * ec[i].i - bk * ec[i].r;
                            end;
                         gen_reg   :
                            begin
                            dpdt[i,j] := ak * ec[i].i - bk * ec[i].r;
                            dqdt[i,j] := -(ak * ec[i].r + bk * ec[i].i);
                            end;
                        end;
                    end;
                 gen_reg   :
                    begin
                    case bustype[j] of
                         load, gen_highvar, gen_lowvar  :
                            begin
                            dpdt[i,j] := ak * ec[i].i - bk * ec[i].r;
                            dpde[i,j] := ak * ec[i].r + bk * ec[i].i;
                            end;
                         gen_reg   :
                            begin
                            dpdt[i,j] := ak * ec[i].i - bk * ec[i].r;
                            end;
                        end;
                    end;
                end;
            end;
        end
        else if i=j then
            begin
            cn[i].r := cn[i].r + ec[i].r * y[i,i].r - ec[i].i * y[i,i].i;
            cn[i].i := cn[i].i + ec[i].r * y[i,i].i + ec[i].i * y[i,i].r;
            end;
    end;   { row i now complete except for diagonal terms, mismatch etc. }

p_net_inj[i] := ec[i].r * cn[i].r + ec[i].i * cn[i].i;
q_net_inj[i] := ec[i].i * cn[i].r - ec[i].r * cn[i].i;

{
writeln(i,p_net_inj[i]:11:4,q_net_inj[i]:11:4,
                      p_sched_inj[i]:11:4,q_sched_inj[i]:11:4);
}

case bustype[i] of
     load, gen_highvar, gen_lowvar  :
        begin
        delp[i] := p_sched_inj[i] - p_net_inj[i];
        delq[i] := q_sched_inj[i] - q_net_inj[i];
        if abs( delp[i] ) > p_max_mismatch then
                  p_max_mismatch := abs( delp[i] );
        if abs( delq[i] ) > q_max_mismatch then
                  q_max_mismatch := abs( delq[i] );
        em2 := ep[i].m * ep[i].m;
        dpdt[i,i] :=  - q_net_inj[i] - y[i,i].i * em2;
        dpde[i,i] :=    p_net_inj[i] + y[i,i].r * em2;
        dqdt[i,i] :=    p_net_inj[i] - y[i,i].r * em2;
        dqde[i,i] :=    q_net_inj[i] - y[i,i].i * em2;
        end;
     gen_reg   :
        begin
        delp[i] := p_sched_inj[i] - p_net_inj[i];
        if abs( delp[i] ) > p_max_mismatch then
                  p_max_mismatch := abs( delp[i] );
        em2 := ep[i].m * ep[i].m;
        dpdt[i,i] :=  - q_net_inj[i] - y[i,i].i * em2;
        end;
    end;
end;

{  done calculating jacobian, see if solution is done }

writeln('**************************************************************');
writeln;
writeln('                    ITERATION ',iter);
writeln;
writeln('The maximum P mismatch is ',p_max_mismatch:11:4);
writeln('The maximum Q mismatch is ',q_max_mismatch:11:4);
writeln;

if ( ( p_max_mismatch < max_mismatch_newton )
 and ( q_max_mismatch < max_mismatch_newton ) ) then goto skip ;

{ factor jacobian and perform foreward operations on delp and delq }

for i := 1 to numbuses do
begin

case bustype[i] of
 load , gen_reg, gen_highvar, gen_lowvar   :
    begin
    for j := 1 to numbuses do
        begin
        if j = i then      { invert diagonal and normalize row }
            begin
            case bustype[i] of
                 load, gen_highvar, gen_lowvar :
                    begin
                    detd := dpdt[i,i] * dqde[i,i] - dqdt[i,i] * dpde[i,i];
                    d11 := dqde[i,i] / detd;
                    d12 := - dpde[i,i] / detd;
                    d21 := - dqdt[i,i] / detd;
                    d22 := dpdt[i,i] / detd;
                    end;
                 gen_reg  :
                    begin
                    d11 := 1.0 / dpdt[i,i];
                    d12 := 0.0;
                    d21 := 0.0;
                    d22 := 0.0;
                    end;
                end;
                temp_delp := d11 * delp[i] + d12 * delq[i];
                temp_delq := d21 * delp[i] + d22 * delq[i];
                delp[i] := temp_delp;
                delq[i] := temp_delq;
                for k := i to numbuses do
                    begin
                    temp_dpdt := d11 * dpdt[i,k] + d12 * dqdt[i,k];
                    temp_dpde := d11 * dpde[i,k] + d12 * dqde[i,k];
                    temp_dqdt := d21 * dpdt[i,k] + d22 * dqdt[i,k];
                    temp_dqde := d21 * dpde[i,k] + d22 * dqde[i,k];
                    dpdt[i,k] := temp_dpdt;
                    dpde[i,k] := temp_dpde;
                    dqdt[i,k] := temp_dqdt;
                    dqde[i,k] := temp_dqde;
                    end;
            end
        else if j < i then      { eliminate terms to left of diagonal }
            begin
            if ( abs(dpdt[i,j]) + abs(dqdt[i,j]) + abs(dqde[i,j])  > 0.0) then
                begin
                temp_dpdt := dpdt[i,j];
                temp_dpde := dpde[i,j];
                temp_dqdt := dqdt[i,j];
                temp_dqde := dqde[i,j];
                delp[i] := delp[i] -
                             ( temp_dpdt * delp[j] + temp_dpde * delq[j] );
                delq[i] := delq[i] -
                             ( temp_dqdt * delp[j] + temp_dqde * delq[j] );
                for k := j to numbuses do
                    begin
                    dpdt[i,k] := dpdt[i,k] -
                          ( temp_dpdt * dpdt[j,k] + temp_dpde * dqdt[j,k] );
                    dpde[i,k] := dpde[i,k] -
                          ( temp_dpdt * dpde[j,k] + temp_dpde * dqde[j,k] );
                    dqdt[i,k] := dqdt[i,k] -
                          ( temp_dqdt * dpdt[j,k] + temp_dqde * dqdt[j,k] );
                    dqde[i,k] := dqde[i,k] -
                          ( temp_dqdt * dpde[j,k] + temp_dqde * dqde[j,k] );
                    end;
                end;
            end;
        end;
    end;
end;

end;  { end of jacobian factoring }

{  calculate dele and delang by back substitution }

for i := numbuses downto 1 do
    begin
    delang[i] := delp[i] ;
    dele[i] := delq[i] ;
    if i < numbuses then
        begin
        for j := i+1 to numbuses do
            begin
            delang[i] := delang[i] -
                       ( dpdt[i,j] * delang[j] + dpde[i,j] * dele[j] );
            dele[i] := dele[i] -
                       ( dqdt[i,j] * delang[j] + dqde[i,j] * dele[j] );
            end;
        end;
    end;

{ update the voltages and phase angles to new values using dele and delang }

for i := 1 to numbuses do
    begin
    ep[i].a := ep[i].a + delang[i];
    ep[i].m := ep[i].m * ( 1.0 + dele[i] );
    ec[i].r := ep[i].m * cos( ep[i].a );
    ec[i].i := ep[i].m * sin( ep[i].a );
    {
    writeln(i,'  ',dele[i]:11:6,'  ',delang[i]:11:6,'  ',ep[i].m:7:3,'  ',
                       (180./3.14159)*ep[i].a:7:2 );
    }
    end;


skip :

if ( ( p_max_mismatch < 10.0 * max_mismatch_newton ) 
     and
     ( q_max_mismatch < 10.0 * max_mismatch_newton ) )  then check_gen_vars;

until ( ( iter > maxiter_newton )
        or
        (    ( p_max_mismatch < max_mismatch_newton )
         and ( q_max_mismatch < max_mismatch_newton ) 
         and no_var_limiting                 ) );


end;          { end of newton load flow solution }

{----------------------------------------------------------------------------}
procedure output_data( var dev:text);
var
    i,j,busno:integer;
begin { output_data }
{
  writeln(dev);
  writeln(dev,'The elements of the Y matrix are:');
  writeln(dev);
  for i := 1 to numbuses do
    for j := 1 to numbuses do
      writeln(dev,'y(',i:2,',',j:2,') = (',y[i,j].r:8:4,') + j(',y[i,j].i:8:4,')');
 }
  writeln(dev);
  writeln(dev,'file: ',filename );
  writeln(dev);
  writeln(dev,title1);
  writeln(dev,title2);
  writeln(dev);
  writeln(dev,' Number of Buses = ',numbuses );
  writeln(dev,' Number of Lines = ',numlines );
  writeln(dev,' Number of Generators = ',numgen );
  writeln(dev,' Number of Transformers = ', numtran );
  writeln(dev,' Swing Bus at bus number ',swingbus );
  writeln(dev);

  { write out input bus data }

  writeln(dev);
  writeln(dev,'Bus Data');
  writeln(dev);
  writeln(dev,'Bus                                       Voltage     Voltage     Bus  ');
  writeln(dev,'Number  Bus Name   Mw Load    Mvar Load   High Limit  Low limit   Type ');
  writeln(dev,'------  --------  ----------  ----------  ----------  ----------  -----');
  for busno := 1 to numbuses do
    begin
    write(dev,busno:6,'  ');
    write(dev,busname[busno],'  ');
    write(dev,100*pload[busno]:10:5,'  ');
    write(dev,100*qload[busno]:10:5,'  ');
    write(dev,volt_high_limit[busno]:10:5,'  ');
    write(dev,volt_low_limit[busno]:10:5,'  ');
    case bustype[busno] of
      load  : writeln(dev,'LOAD');
      gen_reg, gen_highvar, gen_lowvar   : writeln(dev,'GEN');
      swing : writeln(dev,'SWING');
      end;
    end;

  { write out input generator data }

  writeln(dev);
  writeln(dev,'Generator Data ');
  writeln(dev);
  writeln(dev,'Bus     Mw          Scheduled  High Mvar  Low MVar ');
  writeln(dev,'number  Generation  Voltage    Limit      Limit    ');
  writeln(dev,'------  ----------  ---------  ---------  ---------');
  for i := 1 to numgen do
    begin
    write(dev,genbusno[i]:6,'  ');
    write(dev,pgen[i]:10:5,'  ');
    write(dev,vsched[i]:9:4,'  ');
    write(dev,qmax[i]:9:4,'  ');
    writeln(dev,qmin[i]:9:4);
    end;

  { write out input line data }

  writeln(dev);
  writeln(dev,'Branch Data');
  writeln(dev);
  writeln(dev,'From  To    Branch  Branch  Line      Branch     Branch  Tap   Non-Tap  Tap   ');
  writeln(dev,'Bus   Bus     R       X     Charging  Mva Limit  Type    Bus   Bus      Ratio ');
  writeln(dev,'----  ----  ------  ------  --------  ---------  ------  ----  -------  ------');
  for i := 1 to numlines_dbl do if frombus[i] < tobus[i] then
    begin
    write(dev,frombus[i]:4,'  ');
    write(dev,tobus[i]:4,'  ');
    write(dev,r[i]:6:4,'  ');
    write(dev,x[i]:6:4,'  ');
    write(dev,bcap[i]:8:6,'  ');
    write(dev,linelimit[i]:9:4,'   ');
    write(dev,linetype[i],'  ');
    if linetype[i] = 'TRAN' then
      begin
      j := tran_pointer[ i ];
      write(dev,tapbus[j]:4);
      write(dev,nontapbus[j]:7);
      writeln(dev,tapratio[j]:6:4);
      end;
    writeln(dev);
    end;

    writeln(dev);

end; { output_data }
{----------------------------------------------------------------------------}
procedure output_solution( var dev:text);
var
    i,j,fbus,tbus,bran:integer;
    soffdia,flow,charging,charging_current,line_current,volt_diff : complex;
    mva, plosses,qlosses,
         pgen_total,qgen_total,
         pload_total,qload_total,
         total_i2r, total_i2x,total_charging : real;
    line_current_mag, ymag, line_r, line_x, emag_fbus : real;
begin { output_solution }

{ calculate generator p and q    }

pgen_total := 0.0;
qgen_total := 0.0;
for i := 1 to numgen do
  begin
  j := genbusno[i];
  if bustype[j] = swing then
    begin
    pgen[i] :=  p_net_inj[j] + pload[j];
    qgen[i] :=  q_net_inj[j] + qload[j];
    end
  else
    begin
    qgen[i] := q_net_inj[j] + qload[j];
    end;

    pgen_total := pgen_total + pgen[i];
    qgen_total := qgen_total + qgen[i];
  end;

pload_total := 0.0;
qload_total := 0.0;
for i := 1 to numbuses do
    begin
    pload_total := pload_total + pload[i];
    qload_total := qload_total + qload[i];
    end;

total_i2r := 0.0;
total_i2x := 0.0;
total_charging := 0.0;

  { write out the solution }

  writeln(dev);
  writeln(dev,'Load Flow Solution:');
  writeln(dev);
  writeln(dev,'file: ',filename );
  writeln(dev);
  writeln(dev,title1);
  writeln(dev,title2);
  writeln(dev);
  writeln(dev,'From Volt.  Volt.   Mw      Mvar     Mw     Mvar   To    Mw      Mvar    Mva   ');
  writeln(dev,'Bus  Mag.   Angle   Load    Load     Gen.   Gen.   Bus   Flow    Flow    Flow  ');
  writeln(dev,'---- ------ ------ ------- ------- ------- ------- ---- ------- ------- -------');

  fbus := 0;
  for bran := 1 to numlines_dbl do
    begin
    if fbus <> frombus[bran] then
      begin
      fbus := frombus[bran];
      writeln(dev);
      write(dev,fbus:4,' ');
      write(dev,ep[fbus].m:6:4,' ');
      write(dev,dpr*ep[fbus].a:6:3,' ');
      write(dev,100.0*pload[fbus]:7:2,' ');
      write(dev,100.0*qload[fbus]:7:2,' ');
      if bustype[fbus] in [gen_reg,gen_highvar,gen_lowvar,swing] then
        begin
        i:=1;
        while genbusno[i]<>fbus do i:=i+1;
        write(dev,100.0*pgen[i]:7:2,' ');
        write(dev,100.0*qgen[i]:7:2,' ');
        end;
      writeln(dev);
      end;
    tbus := tobus[bran];
    for i:=1 to 51 do write(dev,' ');
    write(dev,tbus:4,' ');
    {                                                      }
    { calculate the flow into the branch from fbus to tbus }
    {                                                      }
    csub(volt_diff,ec[fbus],ec[tbus]);
    cmult(line_current,volt_diff,y[fbus,tbus]);
    if ( fbus < tbus ) then
        begin
        cmag( line_current_mag, line_current );
        cmag( ymag, y[fbus,tbus] );
        line_r := -y[fbus,tbus].r / ( ymag * ymag );
        line_x :=  y[fbus,tbus].i / ( ymag * ymag );
        total_i2r := total_i2r + line_r * line_current_mag * line_current_mag;
        total_i2x := total_i2x + line_x * line_current_mag * line_current_mag;
        end;
    cmag( emag_fbus, ec[fbus] );
    total_charging := total_charging + bcap[bran] * emag_fbus * emag_fbus;
    charging.r := 0.0;
    charging.i := bcap[bran];
    cmult(charging_current,ec[fbus],charging);
    csub(line_current,charging_current,line_current);
    conj(line_current,line_current);
    cmult(flow,line_current,ec[fbus]);
    mva := sqrt(flow.r * flow.r + flow.i * flow.i);
    {                                 }
    { write out the tbus and the flow }
    {                                 }
    write(dev,100.0*flow.r:7:2,' ');
    write(dev,100.0*flow.i:7:2,' ');
    writeln(dev,100.0*mva:7:2);
    end;

writeln(dev);
writeln(dev);
writeln(dev, '  Mw gen                 = ',100.0*pgen_total:7:2);
writeln(dev, '  Mvar gen               = ',100.0*qgen_total:7:2);
writeln(dev, '  Mw load                = ',100.0*pload_total:7:2);
writeln(dev, '  Mvar load              = ',100.0*qload_total:7:2);
writeln(dev, '  Total I2R Mw losses    = ',100.0*total_i2r:7:2);
writeln(dev, '  Total I2X Mvar losses  = ',100.0*total_i2x:7:2);
writeln(dev, '  Total charging Mvar    = ',100.0*total_charging:7:2);
end;  { output solution }
{----------------------------------------------------------------------------}
procedure gauss_solution;
var
    i,j,k,l,
    fbus,max_volterrorbus:integer;
    soffdia,temp1,temp2:complex;
    max_volterror,magdiff_voltage:real;

    p_jq : complex;

procedure update;

{ updates the voltage at the from bus (fbus)      }
{ if the from bus is a generator bus then the     }
{ reactive scheduled power is updated as well.    }

var
    e,temp1,temp2,diff_voltage,old_voltage:complex;
    epolar:polar;
begin { update }

  { save the old from bus voltage }

  old_voltage := ec[fbus];

  { get the new from bus voltage into the variable e and epolar }

  p_jq.r := p_sched_inj[fbus];
  p_jq.i := q_sched_inj[fbus];
  cdiv(temp1,p_jq,ec[fbus]);
  conj(temp1,temp1);
  sumoffdia(soffdia,fbus);
  csub(temp1,temp1,soffdia);
  cdiv(e,temp1,y[fbus,fbus]);
  cart_to_polar(epolar,e);
  {                                                              }
  { if the bus is a generator bus then set the voltage magnitude }
  { to the scheduled magnitude and calculate a new reactive      }
  { scheduled power.                                             }
  {                                                              }
  if bustype[fbus] = gen_reg then
    begin
    epolar.m := ep[fbus].m;
    polar_to_cart(e,epolar);
    cmult(temp1,y[fbus,fbus],e);
    cadd(temp1,temp1,soffdia);
    conj(temp1,temp1);
    cmult(temp1,temp1,e);
    q_sched_inj[fbus] := temp1.i;
    end;
  {                          }
  { save the new bus voltage }
  ec[fbus]:=e;
  ep[fbus]:=epolar;
  {                                }
  { save largest change in voltage }
  {                                }
  csub(diff_voltage,old_voltage,ec[fbus]);
  magdiff_voltage := sqrt (diff_voltage.r * diff_voltage.r +
                           diff_voltage.i * diff_voltage.i);
  if magdiff_voltage > max_volterror then
    begin
      max_volterror := magdiff_voltage;
      max_volterrorbus := fbus;
    end;
end; { update }
begin { gauss_solution }
  iter :=0;
  repeat
    iter := iter + 1;
    max_volterror := 0.0;
    max_volterrorbus := 0;
    for fbus :=1 to numbuses do if bustype[fbus] <> swing then update;
    writeln('**************************************************************');
    writeln;
    writeln('                    ITERATION ',iter);
    writeln;
    write('Maximum change in the voltage is ',max_volterror:9:5);
    writeln(' at bus ',max_volterrorbus:1);
    writeln;
    calc_net_power;
    if ( max_volterror < 10.0 * max_volterror_gauss ) then 
        begin
        check_gen_vars;
        end;
  until (iter > maxiter_gauss ) 
        or
        ( ( max_volterror < max_volterror_gauss )
          and ( no_var_limiting ) );

end; { gauss_solution }


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
procedure change_case;

var i, busno : integer;

procedure change_system_load;

var i : integer;
    total_load, new_load : real;

begin

total_load := 0.0;

for i := 1 to numbuses do
    total_load := total_load + pload[i];


writeln( ' Present total system MW load = ',100.0*total_load:7:2 );
writeln;
write(   ' Enter new total load MW: '); numinput( new_load );
new_load := new_load / 100.0 ;

for i := 1 to numbuses do
    begin
    pload[i] := pload[i] * new_load / total_load;
    qload[i] := qload[i] * new_load / total_load;
    end;

end;

procedure change_gen_volts;

var  busno,i : integer;
     newvolt : real;

begin

repeat
writeln( ' Present generator voltages are : ');
writeln;
for i := 1 to numgen do
    writeln('  Generator bus ',genbusno[i]:2,' PU sched voltage = ',
                vsched[i]:5:3 );

writeln( ' Enter generator bus number, a space, new PU scheduled voltage');
writeln( ' (enter 0 0 to terminate ): ' ); read( busno ); numinput( newvolt );

if busno <> 0 then
    begin
    for i := 1 to numgen do
    if genbusno[i] = busno then
        vsched[i] := newvolt;
    end;

until busno = 0;

end;

procedure change_gen_mw;

var busno,i : integer;
    newmw : real;

begin

repeat
writeln( ' Present generator MW schedules are : ');
writeln;
for i := 1 to numgen do
    writeln('  Generator bus ',genbusno[i]:2,' scheduled MW = ',
                100.0*pgen[i]:7:2 );

writeln( ' Enter generator bus number, a space, new scheduled MW ');
writeln( ' (enter 0 0 to terminate ): ' ); read( busno ); numinput( newmw );

if busno <> 0 then
    begin
    for i := 1 to numgen do
    if genbusno[i] = busno then
        pgen[i] := newmw / 100.0 ;
    end;

until busno = 0;

end;

begin

  repeat
    writeln;
    writeln(' Change Input Data Options:');
    writeln;
    writeln('1 - change system load');
    writeln('2 - change generator scheduled voltage');
    writeln('3 - change generator scheduled MW');
    writeln('4 - Return to main menu');
    writeln;
    write('Enter option >');
    readln(i);
    if i in [1,2,3] then
      case i of
      1 : change_system_load;
      2 : change_gen_volts;
      3 : change_gen_mw;
      end;
  until i = 4;

{ rebuild bus lists }

for i := 1 to numbuses do
      begin
      p_sched_inj[i] := -pload[i];
      q_sched_inj[i] := -qload[i];
      ep[i].m := 1.0;
      ep[i].a := 0.0;
      ec[i].r := 1.0;
      ec[i].i := 0.0;
      bustype[i] :=  load ;
      end;

for i := 1 to numgen do
      begin
      busno := genbusno[i];
      p_sched_inj[busno] := p_sched_inj[busno] + pgen[i];
      bustype[busno] :=  gen_reg  ;
      ep[busno].m := vsched[i];
      ec[busno].r := vsched[i];
      end;

bustype[ swingbus ] :=  swing ;


end;

{----------------------------------------------------------------------------}
begin  { loadflow }

  zero.r:=0.0;
  zero.i:=0.0;

  datainput;
         if ioerr then goto quit;

  repeat
    writeln;
    writeln(' Menu of options:');
    writeln;
    writeln('1 - print input data');
    writeln('2 - run Gauss-Seidel loadflow');
    writeln('3 - run Newton-Raphson loadflow');
    writeln('4 - print solution');
    writeln('5 - change input data');
    writeln('6 - write voltage solution to a file');
    writeln('7 - quit');
    writeln;
    write('Enter option >');
    readln(i);
    if i in [1..7] then
      case i of
      1 :begin
         if ( output_device = 'display' ) then output_data(output);
         if ( output_device = 'printer' ) then output_data(lst);
         end;
      2 : gauss_solution;
      3 : newton_solution;
      4 :begin
         if ( output_device = 'display' ) then output_solution(output);
         if ( output_device = 'printer' ) then output_solution(lst);
         end;
      5 : change_case;
      6 : file_solution;
      end;
  until i = 7;

quit:

end. { loadflow }

