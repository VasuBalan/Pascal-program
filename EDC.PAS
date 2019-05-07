{$R-}    {Range checking off}
{$B+}    {Boolean complete evaluation on} 
{$S+}    {Stack checking on} 
{$I+}    {I/O checking on}
{$N-}    {No numeric coprocessor}
{$M 65500,16384,655360} {Turbo 3 default stack and heap}

{ $LINESIZE:110}
{ $PAGESIZE:48}
{ $DEBUG+}
{ $LINE+}

{ -------------------------------------------------------------------}
{            Economic Dispatch Program from Chapter 3                }
{             POWER GENERATION OPERATION AND CONTROL                 }
{              Allen J. Wood and Bruce F. Wollenberg                 }
{ -------------------------------------------------------------------}
{ngen                             Number of generators                 }
{curvetype                        Type of cost curve                   }
{                                   poly = Polynomial                  }
{                                   pinc = Piecewize incremental       }
{                                   pio  = Piecewize Input/Output      }
{curveorder                       Order or num of points in curve      }
{losstype                         Loss type                            }
{                                   noloss = Losses neglected          }
{                                   constpf = Constant penalty factors }
{                                   lossform = Loss formula            }
{totalgen                         Total generation as specified by user}
{totalloss                        Total transmission losses            }
{lambda                           Incremental cost ( $/MWHR)           }
{diagflag                         Diagnostics flag (N = no diag, Y = diag)}
{b00, b0, b                       Loss matrix coefficients             }
{solution_type                    Solution type                        }
{                                   lamsearch = Lambda search          }
{                                   tbllookup = Table lookup           }
{schedtype                        Schedule type                        }
{                                   totgen = total generation          }
{                                   totload = total load               }
{schedmw                          Schedule MW                          }
{numorder                         Number of entries in ordering routine}


program edc (input, output, inputfile);

uses
         Crt, Printer;

label    quit;

const

         max_units = 20;
         max_order = 10;
         max_curve_points = 10;
         max_total_segments = 200;
         total_gen_tolerance = 0.01 ;
         ihr_tolerance = 0.000001 ;
         ioval : integer = 0;
         ioerr : boolean = false;
         alpha : real = 0.5; {See note in loss matrix procedure}

type

         unit_array_real = array[1..max_units] of real;
         unit_name_array = array[1..max_units] of string[20];
         coefficients = array[0..max_order] of real;
         unit_poly_array = array[1..max_units] of coefficients;
         curve_points = array[0..max_curve_points] of real;
         unit_curve_array = array[1..max_units] of curve_points;
         system_ihr_array_real = array[1..max_total_segments] of real;
         system_ihr_array_integer = array[1..max_total_segments] of integer;
         B_matrix = array[1..max_units] of unit_array_real;
         filename_array = string[25];
         curvetype_list = (poly,pinc,pio);
         losstype_list = (noloss,constpf,lossform);
         solution_type_list = (lamsearch,tbllookup);
         schedtype_list = (totgen,totload);

var

     genname:unit_name_array;           {Generator name identifier}
     p:unit_array_real;                 {Present value of P}
     pmin:unit_array_real;              {Minimum MW}
     pmax:unit_array_real;              {Maximum MW}
     minihr:unit_array_real;            {Minimum unit incremental heat rate}
     maxihr:unit_array_real;            {Maximum unit incremental heat rate}
     fuelcost:unit_array_real;          {Fuel cost ( $/fuel unit )}
     coeff : unit_poly_array;           {Unit polynomial coefficients}
     ihr_mwpoint:unit_curve_array;        {MW points on ihr cost curve}
     ihr_cost:unit_curve_array;           {Cost points for ihr curve}
     io_mwpoint : unit_curve_array;     {MW Points on unit io curve}
     io_cost : unit_curve_array;        {Cost points on io curve}
     minput:unit_array_real;            {Minimum input for PINC curves }
     penfac:unit_array_real;            {Loss penalty factor}
     b00:real;                          {Loss matrix constant}
     b0:unit_array_real;                {Loss matrix linear terms}
     b:B_matrix;                        {Loss matrix quadratic terms}
     seginccost:system_ihr_array_real;  {Segment inc cost for table look up }
     segunit:system_ihr_array_integer;  {Unit associated with segment}
     segmw:system_ihr_array_real;       {MW contributed by segment}
     order:system_ihr_array_integer;    {Order routine output}
     ordvalue:system_ihr_array_real;    {Numbers to be ordered}
     inputfile:text;
     filename:filename_array;
     title1, title2 : string[80];
     print_output, diagflag, read_data : boolean;
     inputchar,quitflag : char;
     linenumber, ngen : integer;
     mwlosses, schedmw, lambda : real;
     curvetype_input, losstype_input : string[8];
     number_string : string[20];
     curveorder : integer;
     curvetype : curvetype_list;
     losstype : losstype_list;
     solution_type : solution_type_list;
     schedtype : schedtype_list;
     pgenmax, pgenmin : real;

{----------------------------------------------------------------------------} 
{ <f> <s>   IO Check routine } 
{$I-,R-} 
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

{ -------------------------------------------------------------------}
{ <f> <s> ihr_ftn }
procedure ihr_ftn(          i : integer;
                       unitmw : real;
                  var unitihr : real );

      { Routine to return unit incremental heat rate given unit output in MW }
      { input : unit index = i}
      {         unit mw = unitmw}
      { output: unit incremental heat rate = unitihr}

var
         partmw : real;
         j : integer;

begin

case curvetype of
  poly :                    {Polynomial I/O curve}
      begin
      unitihr := 0.0;
      for j := curveorder downto 2 do
        unitihr := ( unitihr + j * coeff[ i,j ] ) * unitmw;
      unitihr := unitihr + coeff[ i,1 ]
      end;

  pinc :                     {Piecewize incremental curve}
      begin
      j := 0;
      repeat
      j := j + 1;
      until (ihr_mwpoint[ i,j ] > unitmw) or (j = curveorder);

      partmw := (unitmw - ihr_mwpoint[i,j-1] )/
                       (ihr_mwpoint[i,j] - ihr_mwpoint[i,j-1] );
      unitihr := ihr_cost[i,j-1] + ( ihr_cost[i,j] - ihr_cost[i,j-1] ) * partmw
      end;

  pio  :                     {Piecewize I/O curve}
      begin
      j := 0;
      repeat
      j := j + 1;
      until (io_mwpoint[ i,j ] > unitmw) or (j = curveorder);

      unitihr := (io_cost[i,j] - io_cost[i,j-1] ) /
                          ( io_mwpoint[i,j] - io_mwpoint[i,j-1] )
      end;
  end;  { End of case statement}


end; { End ihr_ftn procedure }

{----------------------------------------------------------------------------}
{ <f> <s>   inverse_ihr_ftn }
procedure inverse_ihr_ftn(       i : integer;
                           unitihr : real;
                        var unitmw : real );

      { Routine to return unit MW given unit incremental heat rate}
      { input : unit number = i}
      {         unit inc heat rate = unitihr}
      { output: unit MW stored in unitmw}

label  return;

var
         unitihr1, delihr, partihr, dihrdp : real;
         segmentihr : real;
         j, step : integer;

begin

if unitihr >= maxihr[ i ] then
    begin
    unitmw := pmax[ i ];
    goto return
    end;
if unitihr <= minihr[ i ] then
    begin
    unitmw := pmin[ i ];
    goto return
    end;

case curvetype of
  poly :                       {Polynomial curve}
      begin
      if curveorder <= 1 then
       begin
       if unitihr > coeff[ i,1 ] then unitmw:=pmax[i] else unitmw:=pmin[i];
       goto return
       end;

      if curveorder = 2 then
       begin
       unitmw := ( unitihr - coeff[ i,1 ] ) / ( 2.0 * coeff[ i,2 ] );
       goto return
       end;

            { for curves of order >= 3 search for unitmw using Newtons method }

      unitmw := ( pmin[ i ] + pmax[ i ] )/ 2.0;
      step := 0;
      repeat
      step := step + 1;

      unitihr1 := 0;                  {Calc unitihr at unitmw as unitihr1}
      for j := curveorder downto 2 do
         unitihr1 := ( unitihr1 + j * coeff[i,j] ) * unitmw;
      unitihr1 := unitihr1 + coeff[i,1];
      delihr := unitihr - unitihr1;
      if abs( delihr ) < ihr_tolerance then goto return;

      dihrdp := 0;                     {Calc curve second derivative}
      for j := curveorder downto 3 do
         dihrdp := ( dihrdp + j*(j-1) * coeff[i,j] ) * unitmw;
      dihrdp := dihrdp + 2.0 * coeff[ i,2 ];
      unitmw := unitmw + delihr/dihrdp;

      until step > 20;

      goto return
      end;

  pinc :                           {Piecewize incremental curve}
      begin
      j := 0 ;
      repeat
      j := j + 1;
      until (ihr_cost[i,j] > unitihr) or
            (j = curveorder);

      partihr := ( unitihr - ihr_cost[i,j-1] )/
                          ( ihr_cost[i,j] - ihr_cost[i,j-1] );
      unitmw := ihr_mwpoint[i,j-1] +
                    ( ihr_mwpoint[i,j] - ihr_mwpoint[i,j-1] ) * partihr;
      goto return
      end;

   pio :                           {Piecewise I/O curve}
      begin
      j := 0;
      repeat
      j := j + 1;
      if j = curveorder then
         begin
         unitmw := io_mwpoint[i,j];
         goto return
         end;
      segmentihr :=(io_cost[i,j] - io_cost[i,j-1]) /
                           (io_mwpoint[i,j] - io_mwpoint[i,j-1]);
      until segmentihr >= unitihr;

      unitmw := io_mwpoint[ i,j-1 ];
      goto return
      end;

  end;  { End of case statement}

return:

end; { End procedure }

{----------------------------------------------------------------------------}
{ <f> <s>   loss_matrix_ftn }
procedure loss_matrix_ftn;

      { Routine to calculate losses and penalty factors from loss formula}
      {  Input:   Table of unit generation p[ i ]}
      {           Loss formula b( i,j ), b0[ i ], b00}
      {  Output:  losses mwlosses and penalty factors penfac[ i ]}
      {  Note: loss formula expects p(i)'s to be in per unit so divide by 100.}

var
         i, j : integer;
         incloss, penfac_old, penfac_new : real;

label return;

begin

      mwlosses := b00;
      for i := 1 to ngen do
         begin
         mwlosses := mwlosses + b0[i] *
                        ( p[i]/100.0) + b[i,i] * sqr( p[i]/100.0 );
         for j := i+1 to ngen do
           mwlosses := mwlosses + 2.0 * ( p[i]/100.0) * ( p[j]/100.0 ) * b[i,j]
         end;

      mwlosses := mwlosses * 100.0;
      if print_output then
          writeln(lst, ' mwlosses = ',mwlosses:7:1)
          else
          writeln(' mwlosses = ',mwlosses:7:1);

      for i := 1 to ngen do
         begin
         penfac_old := penfac[ i ];
         incloss := b0[i];
         for j := 1 to ngen do
            incloss := incloss + 2.0 * ( p[j]/100.0 ) * b[i,j];
         penfac_new := 1.0 / ( 1.0 - incloss );
         penfac[ i ] := penfac_old + alpha *
                                      ( penfac_new  -  penfac_old)
         end;

{ Note, in the formula above the penalty factor is "filtered" by the }
{ alpha filtering constant. If alpha is set to 1.0 no filtering action }
{ takes place, if alpha is 0.0 penfac is constant at 1.0 , suggested }
{ value for alpha is 0.5 to 0.9 }

return:

end; { End procedure }

{----------------------------------------------------------------------------}
{ <f> <s>   prod_cost }
procedure prod_cost(       i : integer;
                      unitmw : real;
              var   unitcost : real );

      { Routine to return unit production cost given unit output in mw}
      { input : unit index = i}
      {         unit MW =  unitmw}
      { output: unit production cost = unitcost}

var
       j : integer;
       partmw, unitihr, segmentcost : real;

label return;

begin

case curvetype of
  poly :                         {Polynomial I/O curve}
      begin
      unitcost := 0;
      for j := curveorder downto 1 do
      unitcost := ( unitcost + coeff[ i,j ] ) * unitmw;

      unitcost := unitcost + coeff[ i,0 ];
      unitcost := unitcost * fuelcost[ i ];
      goto return
      end;

  pinc :                         {Piecewize incremental curve}
      begin
      unitcost := minput[ i ] * fuelcost[ i ];
      for j := 1 to curveorder do
         begin
         if (unitmw > ihr_mwpoint[ i,j ]) and ( j < curveorder ) then
                         {Calculate area under complete segment}
            begin
            segmentcost :=  ( (ihr_cost[i,j] + ihr_cost[i,j-1] )/2.0 ) *
                            ( ihr_mwpoint[i,j] - ihr_mwpoint[i,j-1] ) *
                                    fuelcost[ i ];
            unitcost := unitcost + segmentcost;
            end
            else
                         {Calculate area under partial segment}
            begin
            partmw := (unitmw - ihr_mwpoint[i,j-1] )/
                            (ihr_mwpoint[i,j] - ihr_mwpoint[i,j-1] );
            unitihr := ihr_cost[i,j-1] +
                           ( ihr_cost[i,j] - ihr_cost[i,j-1] ) * partmw;
            segmentcost :=  ( (unitihr + ihr_cost[i,j-1])/ 2.0 ) *
                             ( unitmw - ihr_mwpoint[i,j-1] )  *
                             fuelcost[ i ];
            unitcost := unitcost + segmentcost;

            goto return;
            end;
         end;

      end;

   pio :                          {Piecewize I/O curve}
      begin
      for j := 1 to curveorder do
         begin
         if io_mwpoint[i,j] > unitmw then
            begin
            partmw := (unitmw-io_mwpoint[i,j-1] ) /
                              (io_mwpoint[i,j]-io_mwpoint[i,j-1] );
            unitcost := io_cost[i,j-1] +
                             ( io_cost[i,j]-io_cost[i,j-1] ) * partmw;
            unitcost := unitcost * fuelcost[ i ];
            goto return
            end;
         if j = curveorder then     {Unit is at or above pmax}
            begin
            unitcost := io_cost[ i, j ] * fuelcost[ i ];
            goto return
            end;
         end;
      end;
  end;  { End of case statement}

return:

end; { End procedure }

{----------------------------------------------------------------------------}
{ <f> <s> Lambda search solution routine  }
procedure lambda_search_dispatch( var lambda : real );

var
         i, n, lossiter : integer;
         lambdamin, lambdamax : real;
         lambdastart, deltalambda, targetgen : real;
         unitihr, unitmw, totalgen : real;
         endloop : boolean;

begin

for i := 1 to ngen do                    { Set unit output to midrange}
  begin
  p[ i ] := ( pmin[ i ] + pmax[ i ] ) / 2.0
  end;

lossiter := 0;
endloop := false;

repeat                                    {Top of iterative loop with losses}

  lambdamin := 10000.0;
  lambdamax := 0.0;

  if losstype = lossform then   { Calc losses and pen factors}
  begin
  loss_matrix_ftn;
  if diagflag then
     if print_output then
       begin
        writeln(lst,' mw losses = ',mwlosses:10:1)
       end
       else
       begin
        writeln(' mw losses = ',mwlosses:10:1)
       end;
  end;

  for i := 1 to ngen do                  {Calculate max and min lambdas}
    begin
    lambda := maxihr[ i ] * penfac[ i ] * fuelcost[ i ];
    if lambda > lambdamax then lambdamax := lambda;
    lambda := minihr[ i ] * penfac[ i ] * fuelcost[ i ];
    if lambda < lambdamin then lambdamin := lambda
    end;

  if diagflag then
     if print_output then
       begin
        writeln(lst,' lambda limits = ',lambdamin:10:4,lambdamax:10:4)
       end
       else
       begin
        writeln(' lambda limits = ',lambdamin:10:4,lambdamax:10:4)
       end;

  lambdastart := ( lambdamax + lambdamin ) / 2.0;
  deltalambda := ( lambdamax - lambdamin ) / 2.0;

  if diagflag then
   if print_output then
   begin
   writeln(lst,' lambdastart deltalambda = ',lambdastart:10:4,deltalambda:10:4);
   end
   else
   begin
   writeln(' lambdastart deltalambda = ',lambdastart:10:4,deltalambda:10:4);
   end;

  {Set up total generation target}

  if schedtype = totgen then targetgen := schedmw;
  if schedtype = totload then targetgen := schedmw + mwlosses;

  {Lambda search}

  lambda := lambdastart;
  if diagflag then
    if print_output then
       begin
         writeln(lst, ' targetgen = ',targetgen:10:1);
       end
       else
       begin
         writeln(' targetgen = ',targetgen:10:1);
       end;

  n := 0;
  repeat                            {Top of lambda search loop}
      n := n + 1;
      totalgen := 0;
      for i := 1 to ngen do
         begin
         unitihr := lambda / ( penfac[ i ] * fuelcost[ i ] )  ;
         inverse_ihr_ftn( i, unitihr, unitmw );  {For given unitihr get unitmw}
         p[ i ] := unitmw;
         totalgen := totalgen + p[ i ]
         end;

      if diagflag then
       if print_output then
         begin
           writeln(lst,' lambda = ',lambda:10:4,'  totalgen = ',totalgen:10:1);
         end
         else
         begin
           writeln(' lambda = ',lambda:10:4,'  totalgen = ',totalgen:10:1);
         end;

      if abs( totalgen - targetgen ) >= total_gen_tolerance then
        begin
        if totalgen > targetgen then lambda := lambda - deltalambda;
        if totalgen < targetgen then lambda := lambda + deltalambda;
        deltalambda := deltalambda / 2.0
        end;

      until ( abs( totalgen - targetgen ) < total_gen_tolerance ) or
            ( n > 20 ) ;

{See if another loss iteration is needed}

      if losstype <> lossform then endloop := true;
      lossiter := lossiter + 1;
      if lossiter > 10 then endloop := true

until endloop;

end; { End Lambda search procedure }

{----------------------------------------------------------------------------}
{ <f> <s>   Order Procedure }
 procedure order_routine(        numorder : integer;
                               ordertable : system_ihr_array_real;
                         var   orderindex : system_ihr_array_integer );

{ subroutine to order a list, least first                             }
{                                                                     }
{ input numorder = the number of items to be ordered                  }
{ input ordertable = the items to be ordered                          }
{ output orderindex = pointer to order value table                    }
{                                                                     }
{ nxt = Table used in order subroutine                                }
{                                                                     }
  var
      stop:boolean;
      i,j,top,last,indx:integer;
      nxt : system_ihr_array_integer;      

  begin
    for i := 1 to numorder do begin
      if (i <= 1) then begin
        top := 1;
        nxt[ 1 ] := 0;
        end
      else begin
        j := top;
        last := 0;
        repeat
          stop := true;
          if (ordertable[ i ] > ordertable[ j ]) then begin
            last := j;
            j := nxt[ j ];
            stop  := (j = 0);
            if (stop) then begin
              nxt[ last ] := i;
              nxt[ i ] := 0;
            end
            end
          else begin
            if (j <> top) then begin
              nxt[ last ] := i;             { j not = top }
              nxt[ i ] := j;
              end
            else begin
              top := i;                     { j = top }
              nxt[ i ] := j;
            end;
          end;
        until stop;
      end;
    end;
    indx := 1;
    j := top;
    repeat
      orderindex[ indx ] := j;
      j := nxt[ j ];
      indx := indx + 1;
    until (j = 0);
  end;
{----------------------------------------------------------------------------}
{ <f> <s>   table_lookup_dispatch}
procedure table_lookup_dispatch( var lambda : real );

      {  Routine to perform economic dispatch by table look up}

var
         targetgen, ptotal, segihr, unitihr : real;
         i, j, k, kseg, kunit, numsegments : integer;
         done : boolean;

label return;

begin

if curvetype <> pio then
      begin
      writeln;
      writeln(' ERROR -- must have piecewize i/o curves to use table lookup ');
      goto return
      end;

if losstype = lossform then loss_matrix_ftn;  { Calc losses and pen factors}

if schedtype = totgen then targetgen := schedmw;
if schedtype = totload then targetgen := schedmw + mwlosses;

kseg := 0;                        {Build segment tables}
for i := 1 to ngen do
   begin
   for j := 1 to curveorder do
      begin
      kseg := kseg + 1;
      segihr := (io_cost[i,j]-io_cost[i,j-1]) /
                        (io_mwpoint[i,j]-io_mwpoint[i,j-1]);
      seginccost[ kseg ] := segihr * fuelcost[ i ] * penfac[ i ];
      segunit[ kseg ] := i;
      segmw[ kseg ] := io_mwpoint[i,j] - io_mwpoint[i,j-1];
      end;
   end;
numsegments := kseg;

                   {Set up for ordering routine}

for k := 1 to numsegments do
       ordvalue[k] := seginccost[k];
order_routine( numsegments, ordvalue, order );    {Call ordering routine}
                                                   {Result in order table}

             {Print segments table in incremental cost order}

if diagflag then
if print_output then
  begin
  writeln(lst);
  writeln(lst,' segment number   inc cost      MW       unit ');
  writeln(lst,' --------------   ----------   ------    ----')
  end
  else
  begin
  writeln;
  writeln(' segment number   inc cost      MW       unit ');
  writeln(' --------------   ----------   ------    ----')
  end;

for k := 1 to numsegments do
begin
kseg := order[ k ];
if diagflag then
   if print_output then
   begin
   writeln(lst,'       ',kseg:3,'       ',seginccost[kseg]:10:4
                 ,segmw[kseg]:10:1,'   ',segunit[kseg]:4)
   end
   else
   begin
   writeln('       ',kseg:3,'       ',seginccost[kseg]:10:4
                 ,segmw[kseg]:10:1,'   ',segunit[kseg]:4);
   end;
end;


      ptotal := 0.0;
      for i := 1 to ngen do
         begin
         p[ i ] := pmin[ i ];
         ptotal := ptotal + p[ i ]
         end;

      done := false;
      k := 0;
      repeat
         k := k + 1;
         kseg := order[ k ];
         kunit := segunit[ kseg ];
         if ( ptotal + segmw[ kseg ] ) < targetgen then
            begin
            p[ kunit ] := p[ kunit ] + segmw[ kseg ];
            ptotal := ptotal + segmw[ kseg ]
            end
            else
            begin
            p[ kunit ] := p[ kunit ] + ( targetgen - ptotal );
            done := true
            end;
      until done;

      lambda := seginccost[ kseg ];

return:

end; { End procedure }

{----------------------------------------------------------------------------}
{ <f> <s>   output_routine}
procedure output_routine( var outfile : text;
                               lambda : real );

var
         limittxt : string[5];
         totalgen, totalcost, totalload : real;
         unitihr, unitinccost, unitcost : real;
         i : integer;

label return;

begin

writeln(outfile);
writeln(outfile,
      'generator  output   limit  inc cost penalty fact  operating cost');
writeln(outfile,
      '             mw             $/mwhr                   $/hr       ');
writeln(outfile,
      '---------  ------   -----  -------- ------------  --------------');

totalgen := 0.0;
totalcost := 0.0;

for i := 1 to ngen do
   begin
   write(outfile,genname[i]:9);
   write(outfile, ' ',p[i]:6:1, '    ');
   limittxt := '     ';
   if abs( p[i] - pmin[i] ) < total_gen_tolerance then limittxt := 'min  ';
   if abs( p[i] - pmax[i] ) < total_gen_tolerance then limittxt := 'max  ' ;
   write(outfile, limittxt );

   ihr_ftn( i, p[ i ], unitihr) ;    {Get unit incremental heat rate}

   unitinccost := unitihr * fuelcost[i];
   write(outfile, unitinccost:9:4);
   write(outfile, '   ',penfac[i]:9:4, '    ');

   prod_cost( i, p[ i ], unitcost );          {Calculate unit operating cost}

   writeln(outfile, '   ',unitcost:9:2);
   totalgen := totalgen + p[i];
   totalcost := totalcost + unitcost;
   end;
writeln(outfile,
         '---------  ------                                 --------------');
write(outfile, ' totals');
write(outfile, totalgen:9:1,
'                                     ', totalcost:9:2);
writeln(outfile);
writeln(outfile, ' lambda = ', lambda:10:4 );
writeln(outfile);

if (schedtype = totgen ) and ( losstype <> lossform ) then goto return;

if schedtype=totload then totalload := schedmw;

if schedtype=totgen then  totalload := totalgen - mwlosses;

writeln(outfile, 'total load = ',totalload:10:1,
               '  total losses = ',mwlosses:10:1);

return:

end; { End procedure }
{----------------------------------------------------------------------------}
{ <f> <s>   data input procedure }

procedure datainput;

label quit;

var i,j,k,jj : integer;
    a : char;

begin
writeln;
print_output := false;
write(' Do you want output on the printer? (y or n): ');
readln( inputchar );
if (inputchar = 'y') or (inputchar = 'Y') then print_output := true;

linenumber := 0;

writeln;
write('Enter name of input file : ');
readln(filename);
assign(inputfile, filename);
     iocheck( linenumber );
     if ioerr then goto quit;
{                   }
{ Open data file    }
{                   }
reset(inputfile);
     iocheck( linenumber );
     if ioerr then goto quit;
writeln;
{                  }
{ Read file header }
{                  }
linenumber := linenumber + 1;
readln( inputfile, title1 );
     iocheck( linenumber );
     if ioerr then goto quit;
linenumber := linenumber + 1;
readln( inputfile, title2 );
     iocheck( linenumber );
     if ioerr then goto quit;

     {                                                    }
     {  Read Number of generators, curve type, loss type  }
     {                                                    }
linenumber := linenumber + 1;
read( inputfile, ngen );
     iocheck( linenumber );
     if ioerr then goto quit;

repeat
read( inputfile, inputchar );
        iocheck( linenumber );
        if ioerr then goto quit;
until inputchar <> ' ';
curvetype_input := inputchar;
repeat
read( inputfile, inputchar );
      iocheck( linenumber );
      if ioerr then goto quit;
if inputchar <>' ' then curvetype_input := curvetype_input + inputchar;
until inputchar = ' ';

read( inputfile, curveorder );
      iocheck( linenumber );
      if ioerr then goto quit;

repeat
read(inputfile, inputchar );
     iocheck( linenumber );
     if ioerr then goto quit;
until inputchar <> ' ';
losstype_input := inputchar;
readln(inputfile);

 {                                                        }
 {  Set up internal variables for curvetype and losstype  }
 {                                                        }

if (curvetype_input = 'poly') or
   (curvetype_input = 'POLY') then curvetype := poly;

if (curvetype_input = 'pinc') or
   (curvetype_input = 'PINC') then curvetype := pinc;

if (curvetype_input = 'pio' ) or
   (curvetype_input = 'PIO' ) then curvetype := pio;

if (losstype_input = 'n'  ) or
   (losstype_input = 'N'  ) then losstype := noloss;

if (losstype_input = 'c'  ) or
   (losstype_input = 'C'  ) then losstype := constpf;

if (losstype_input = 'l'  ) or
   (losstype_input = 'L'  ) then losstype := lossform;


         {                     }
         { Read generator data }
         {                     }

for i := 1 to ngen do
   begin  { Read generator name }
      linenumber := linenumber + 1;
      repeat
      read( inputfile, inputchar );
            iocheck( linenumber );
            if ioerr then goto quit;
      until inputchar <> ' ';
      genname[i] := inputchar;
      repeat
      read( inputfile, inputchar );
            iocheck( linenumber );
            if ioerr then goto quit;
      if inputchar <>' ' then genname[i] := genname[i] + inputchar;
      until inputchar = ' ';
         {                                   }
         { Read generator min, max, fuelcost }
         {                                   }
      readln( inputfile, pmin[i], pmax[i], fuelcost[i] );
            iocheck( linenumber );
            if ioerr then goto quit;
         {                                   }
         { Read generator cost curve data    }
         {                                   }
      case curvetype of
        poly :
               begin  { read polynomial curve data}
               for j := 0 to curveorder do
                 begin
                   linenumber := linenumber + 1;
                   readln( inputfile, coeff[i,j] );
                    iocheck( linenumber );
                    if ioerr then goto quit;
                 end;
               end;

        pinc :
               begin  { read piecewise incremental cost curve data}
               linenumber := linenumber + 1;
               readln( inputfile, minput[i] );
                 iocheck( linenumber );
                 if ioerr then goto quit;
               for j := 0 to curveorder  do
                 begin
                   linenumber := linenumber + 1;
                   readln( inputfile, ihr_mwpoint[i,j], ihr_cost[i,j] );
                     iocheck( linenumber );
                     if ioerr then goto quit;
                 end;
               end;

        pio  :
               begin  { read piecewise I/O curve data}
               for j := 0 to curveorder do
                 begin
                   linenumber := linenumber + 1;
                   readln( inputfile, io_mwpoint[i,j], io_cost[i,j] );
                     iocheck( linenumber );
                     if ioerr then goto quit;
                 end;
               end;

        end;  { End of case statement}
   end;
         {                }
         { Read loss data }
         {                }

case losstype of

  noloss :
        begin
        for i := 1 to ngen do      { Init penalty factors}
              penfac[ i ] := 1.0
        end;

  constpf  :
      begin   { read constant penalty factor data}
        linenumber := linenumber + 1;
        for i := 1 to  ngen do
         begin
         if i < ngen then
         read( inputfile, penfac[i] )
         else
         readln( inputfile, penfac[ngen] );
            iocheck( linenumber );
            if ioerr then goto quit
         end;
      end;

  lossform :

      begin  { read loss formula data}

      linenumber := linenumber + 1;
      readln( inputfile, b00 );
            iocheck( linenumber );
            if ioerr then goto quit;

      linenumber := linenumber + 1;
      for j := 1 to  ngen  do
        begin
        if j < ngen then
           read( inputfile, b0[ j ] )
           else
           readln( inputfile, b0[ngen] );
            iocheck( linenumber );
            if ioerr then goto quit;
        end;

      for i := 1 to ngen do
        begin
        linenumber := linenumber + 1;
        for j := 1 to ngen  do
         begin
         if j < ngen then
            read( inputfile, b[ i, j ] )
            else
            readln( inputfile, b[ i, ngen ] );
            iocheck( linenumber );
            if ioerr then goto quit
         end;
        end;

        for i := 1 to ngen do      { Init penalty factors}
              penfac[ i ] := 1.0

      end;

  end;  { End of case statement}


{                                  }
{  End of data input, close file   }
{                                  }

close ( inputfile );

{A very useful table is the incremental cost at the max and min of each unit. }
{These are calculated and stored in tables maxihr and minihr.}
{Also calculate the max and min generation}

pgenmax := 0.0;
pgenmin := 0.0;


for i := 1 to ngen do
  begin
    ihr_ftn( i, pmax[ i ], maxihr[ i ] );
    ihr_ftn( i, pmin[ i ], minihr[ i ] );

{ calculate maximum and minimum generation available from generators }

    pgenmax := pgenmax + pmax[ i ];
    pgenmin := pgenmin + pmin[ i ];

  end;

quit:

end;   { end of data input }

{----------------------------------------------------------------------------}
{ <f> <s>   solution set up  }
procedure sol_setup;

label return;

begin

writeln;
writeln( ' please enter solution method : ');
writeln( '   1 = lambda search ');
writeln( '   2 = table lookup ( pio curves only ) ');
writeln;
write( ' enter 1,or 2 : '); readln( inputchar );
     if inputchar = '1' then solution_type  := lamsearch;
     if inputchar = '2' then solution_type  := tbllookup;

writeln;
write( ' do you want diagnostic printout ? (y/n) : ');readln(inputchar);
 if (inputchar ='Y') or (inputchar = 'y') then diagflag := true
                                          else diagflag := false;

return:

writeln;
writeln( ' Maximum generation is :',pgenmax:10:1);
writeln( ' Minimum generation is :',pgenmin:10:1);
writeln;
writeln( ' please enter schedule type ');
writeln( '   1 = total generation ( mw ) ');
writeln( '   2 = total load ( mw ) ');
writeln;
write( ' enter schedule type:  '); readln( inputchar );
     if inputchar = '1' then
        begin
        schedtype := totgen;         {Set up for total gen dispatch}
        writeln;
        write( ' enter total generation ( mw ) :'); numinput(schedmw)
        end;
     if inputchar = '2' then
        begin
        schedtype := totload;        {Set up for total load dispatch}
        writeln;
        write( ' enter total load ( mw ) : '); numinput(schedmw)
        end;

if (schedmw > pgenmax) or (schedmw < pgenmin) then
     begin
       writeln;
       writeln('ERROR ---- EDC not possible with that scheduled generation');
       writeln;
       goto return;
     end;

end; {End of sol setup routine}

{----------------------------------------------------------------------------}
{ <f> <s>   datadump  }
procedure datadump( var outfile:text );


var
   i,j : integer;

begin


writeln(outfile);
writeln(outfile, title1);
writeln(outfile, title2);
writeln(outfile);
writeln(outfile ,' number of generator units = ',ngen );

case curvetype of
  poly : writeln(outfile ,' unit curve type = poly ');
  pinc : writeln(outfile ,' unit curve type = pinc ');
  pio  : writeln(outfile ,' unit curve type = pio');
  end;  { End of case statement}

writeln(outfile ,' curve order = ',curveorder);

case losstype  of
  noloss :   writeln(outfile ,' network loss representation = noloss ');
  constpf :  writeln(outfile ,' network loss representation = constpf ');
  lossform : writeln(outfile ,' network loss representation = lossform ');
  end;  { End of case statement}

for i := 1 to ngen do
  begin
   writeln(outfile);
   write(outfile, genname[i],' limits = ',pmin[i]:7:2, ' ',pmax[i]:7:2 );
   writeln(outfile, ' fuelcost = ',fuelcost[i]:10:4 );

     case curvetype of
         poly :
             begin
             writeln(outfile,'  polynomial coefficients' );
             for j := 0 to curveorder do
               begin
               writeln(outfile, coeff[i,j]:10:4);
               end;
             end;

         pinc :
             begin
             writeln(outfile,' incremental cost curve points');
             writeln(outfile,'input at pmin = ',minput[i]:10:2);
             for j := 0 to curveorder do
               begin
               writeln(outfile,ihr_mwpoint[i,j]:8:2,ihr_cost[i,j]:8:3 )
               end;
             writeln(outfile);
             end;

         pio :
             begin
             writeln(outfile,' cost curve points');
             for j := 0 to curveorder do
               begin
               writeln(outfile,io_mwpoint[i,j]:9:2,'  ',io_cost[i,j]:8:3 )
               end;
             writeln(outfile);
             end;

         end; {end of case statement }

  end;

case losstype  of

  constpf :
                 begin
                 writeln(outfile);
                 writeln(outfile,' Penalty Factors');
                 for i := 1 to ngen do
                   begin
                   writeln(outfile,' penalty factor ',i,' ',penfac[i]:10:3)
                   end;
                 writeln(outfile);
                 end;

  lossform :
                 begin
                 writeln(outfile);
                 writeln(outfile,' Loss Formula');
                 writeln(outfile,'B00 = ',b00:10:4);
                 writeln(outfile);
                 writeln(outfile,'B0 = ');
                 for i := 1 to ngen do
                    if i < ngen then
                    write(outfile,b0[i]:10:4,' ')
                    else
                    writeln(outfile,b0[i]:10:4);
                 writeln(outfile);
                 writeln(outfile,' B = ');
                 for i := 1 to ngen do
                    begin
                         for j := 1 to ngen do
                            if j < ngen then
                            write(outfile,b[i,j]:10:4,' ')
                            else
                            writeln(outfile,b[i,ngen]:10:4);
                    end;
                 writeln(outfile)
                 end;

  end;  { End of case statement}

if print_output then
    if solution_type = lamsearch then writeln(lst,'using lambda search')
                                 else writeln(lst,'using tablelookup');

if print_output then
   begin
       writeln(lst);
       if schedtype = totgen then
          writeln(lst, ' total generation schedule = ',schedmw:10:1)
       else
          writeln(lst, ' total load schedule = ', schedmw:10:1);
       if losstype = lossform then writeln(lst, ' using loss formula ')
                              else writeln(lst,' losses neglected');
       writeln(lst);
   end
   else
   begin
       writeln;
       if schedtype = totgen then
          writeln( ' total generation schedule = ',schedmw:10:1)
       else
          writeln( ' total load schedule = ', schedmw:10:1);
       if losstype = lossform then writeln(' using loss formula ')
                              else writeln(' losses neglected');
       writeln
   end;


end; { End procedure }

{ ---------------------------------------------------------------------}

{ <f> <s>   main program }
begin { Begin main program }

read_data := true;

repeat
if read_data then
  begin
  datainput;                  {Call input routine to read gen data}
   if ioerr then goto quit
  end;

sol_setup;                    {Set up solution paramaters}

if print_output then datadump(lst)
                else datadump(output);    {Call routine to dump input data }

if solution_type = lamsearch  then lambda_search_dispatch( lambda );

if solution_type = tbllookup  then table_lookup_dispatch( lambda );

if print_output then output_routine(lst, lambda )
                else output_routine(output, lambda);

quit:

writeln;
write(' do you want to run edc again? (Y or N) : '); readln(quitflag);

if (quitflag = 'Y') or (quitflag = 'y') then
   begin
   write(' do you want to read a new data file? (Y or N): ');
   readln(inputchar);
   if (inputchar = 'Y') or (inputchar = 'y') then read_data := true
                                             else read_data := false;
   end;

until (quitflag <> 'Y') and (quitflag <> 'y');

end. { End main program }



