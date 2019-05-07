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

{                                                                     }
{ ------------------------------------------------------------------- }
{                Unit Commitment Program from chapter 5               }
{                POWER GENERATION OPERATION AND CONTROL               }
{                Allen J. Wood and Bruce F. Wollenberg                }
{ ------------------------------------------------------------------- }
{ UNTMIN = Unit minimum MW                                            }
{ UNTMAX = Unit maximum MW                                            }
{ UNTGEN = Unit generation MW                                         }
{ UNTINC = Unit incremental cost R/mwhr                               }
{ UNTNOLOADCOST = Unit no load cost R/hr                              }
{ UNTSTARTCOST = Unit start up cost R                                 }
{ UNTFUELCOST = Unit fuel cost R/MBTU                                 }
{ UNTUPMIN = Unit minimum up time HR                                  }
{ UNTDOWNMIN = Unit minimum down time HR                              }
{ UNTSTATINI = Holds initial unit status                              }
{ SYSLOAD = System load MW                                            }
{ UNTSTAT = Unit status                                               }
{ UNTSTATLAST = Unit status for previous period;                      }
{                        1st index is state                           }
{                        2nd index is unit index                      }
{                        + = on line/ - = off line                    }
{                        absolute value = number of HR                }
{ UNTSTATNOW = Same as UNTSTATLAST but for present period             }
{ UNTSTATTEMP = Holds temporary status during path search             }
{ FCOST = Cost of state at period K                                   }
{ PCOST = System production cost table                                }
{ PATH = Pointer to optimal state last period                         }
{ SETL = List of states in last period                                }
{ SETX = List of states in this period                                }
{ UNTFULLAVECOST = Unit full load average cost                        }
{ ORDERINDEX = Order table returned from ordering subroutine          }
{                                                                     }
PROGRAM UNITCOM(INPUT,OUTPUT,INFILE);



Uses
  Crt,Printer;

LABEL QUIT;

CONST
      INFINITY = 1.0E12;
      MAX_NUMUNITS = 10;
      MAX_NUMSTATES = 256;
      MAX_NUMPERIODS = 8;
      IOVAL : INTEGER = 0;
      IOERR : BOOLEAN = FALSE;

TYPE

     SET_OF_UNIT_NUMBERS = SET OF 1..MAX_NUMUNITS;
     STATE_ARRAY = ARRAY [1..MAX_NUMSTATES] OF SET_OF_UNIT_NUMBERS;
     UNIT_ARRAY_REAL = ARRAY [1..MAX_NUMUNITS] OF REAL;
     UNIT_ARRAY_INTEGER = ARRAY [1..MAX_NUMUNITS] OF INTEGER;
     STATE_ARRAY_REAL = ARRAY [1..MAX_NUMSTATES] OF REAL;
     STATE_ARRAY_INTEGER = ARRAY [1..MAX_NUMSTATES] OF INTEGER;
     STATE_X_UNIT_ARRAY_INTEGER =
                    ARRAY [1..MAX_NUMSTATES] OF UNIT_ARRAY_INTEGER;
     FILENAME_ARRAY = STRING[25];
     PERIOD_REC = RECORD
                 SYSLOAD:REAL;
                 PCOST:STATE_ARRAY_REAL;
                 FCOST:STATE_ARRAY_REAL;
                 PATH:STATE_ARRAY_INTEGER;
               END;
     DP_SOLUTION_ARRAY = ARRAY [0..MAX_NUMPERIODS] OF PERIOD_REC;

VAR

    INFILE:TEXT;
    PERIOD_DATA:DP_SOLUTION_ARRAY;
    UNTMIN:UNIT_ARRAY_REAL;
    UNTMAX:UNIT_ARRAY_REAL;
    UNTGEN:UNIT_ARRAY_REAL;
    UNTINC:UNIT_ARRAY_REAL;
    UNTNOLOADCOST:UNIT_ARRAY_REAL;
    UNTSTARTCOST:UNIT_ARRAY_REAL;
    UNTFUELCOST:UNIT_ARRAY_REAL;
    UNTUPMIN:UNIT_ARRAY_INTEGER;
    UNTDOWNMIN:UNIT_ARRAY_INTEGER;
    UNTSTATINI:UNIT_ARRAY_INTEGER;
    UNTSTAT:STATE_ARRAY;
    UNTSTATLAST:STATE_X_UNIT_ARRAY_INTEGER;
    UNTSTATNOW:STATE_X_UNIT_ARRAY_INTEGER;
    UNTSTATTEMP:UNIT_ARRAY_INTEGER;
    SETL:STATE_ARRAY_INTEGER;
    SETX:STATE_ARRAY_INTEGER;
    ORDERINDEX:STATE_ARRAY_INTEGER;
    UNTFULLAVECOST:STATE_ARRAY_REAL;
    NUMUNT:INTEGER;
    NUMSTAT:INTEGER;
    NUMPER:INTEGER;
    PERIOD_LENGTH:REAL;
    ORDERTYPE:INTEGER;
    I,J,K,M,N,X:INTEGER;
    INPUTCHAR,INCLUDE,QUITFLAG:CHAR;
    NLIM,NMAX,XLIM,XMAX,XSTATE,LSTATE,VALID,OPTSTATE:INTEGER;
    INITSTAT:INTEGER;
    SCOST,PATHCOST,OPTCOST:REAL;
    UNTCOST:REAL;
    FILENAME:FILENAME_ARRAY;
    LINENUMBER : INTEGER;
    STATE:SET_OF_UNIT_NUMBERS;
    CONTINUE,BORROW,PRINT_OUTPUT : BOOLEAN;
    TITLE1, TITLE2 : STRING[80];

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
{! 2. IORes^ult now returns different values corresponding to DOS error codes.}
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

{---------------------------------------------------------------------------}
{ <f> <s>   DATA INPUT PROCEDURE }

PROCEDURE DATAINPUT;

LABEL QUIT;

VAR I,J : INTEGER;
    A : CHAR;

BEGIN

    WRITELN;
    PRINT_OUTPUT := FALSE;
    WRITE(' DO YOU WANT OUTPUT ON THE PRINTER? (Y OR N): ');
    READLN( INPUTCHAR );
    IF (INPUTCHAR = 'Y') OR (INPUTCHAR = 'y') THEN PRINT_OUTPUT := TRUE;

    LINENUMBER := 0;

    WRITELN;
    WRITE('ENTER NAME OF INPUT FILE : ');
    READLN(FILENAME);
    ASSIGN(INFILE,FILENAME);
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;
    {                   }
    { Open data file    }
    {                   }
    RESET(INFILE);
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;
    WRITELN;
    {                  }
    { Read file header }
    {                  }
    LINENUMBER := LINENUMBER + 1;
    READLN( INFILE, TITLE1 );
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;

    LINENUMBER := LINENUMBER + 1;
    READLN( INFILE, TITLE2 );
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;

    {                      }
    { Read number of units }
    {                      }

    LINENUMBER := LINENUMBER + 1;
    READLN(INFILE,NUMUNT);

    {                      }
    { Read unit data       }
    {                      }

    FOR I := 1 TO NUMUNT DO BEGIN

    LINENUMBER := LINENUMBER + 1;
    READLN(INFILE);     {  read past comment for unit I }
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;

    LINENUMBER := LINENUMBER + 1;
    READLN(INFILE,UNTMIN[I], UNTMAX[I], UNTINC[I]);
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;

    LINENUMBER := LINENUMBER + 1;
    READLN(INFILE,UNTNOLOADCOST[I], UNTSTARTCOST[I], UNTFUELCOST[I]);
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;

    LINENUMBER := LINENUMBER + 1;
    READLN(INFILE,UNTUPMIN[I], UNTDOWNMIN[I], UNTSTATINI[I]);
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;
    END;

    {                                          }
    { Read number of periods and period length }
    {                                          }

    LINENUMBER := LINENUMBER + 1;
    READLN(INFILE,NUMPER,PERIOD_LENGTH);
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;

    {                      }
    { Read load curve data }
    {                      }

    FOR I := 1 TO NUMPER DO BEGIN
    LINENUMBER := LINENUMBER + 1;
    READ(INFILE,PERIOD_DATA[I].SYSLOAD);
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;
       END;

    CLOSE (INFILE);
         IOCHECK( LINENUMBER );
         IF IOERR THEN GOTO QUIT;

    {            }
    { User input }
    {            }

    WRITELN;
    WRITELN('SELECT UNIT ORDER OPTION ');
    WRITELN('1 - PRIORITY ORDER ');
    WRITELN('2 - COMPLETE ENUMERATION ');
    WRITELN;
    WRITE('ENTER OPTION NUMBER : ');
    READLN(ORDERTYPE);
    WRITELN;
    WRITE('ENTER NUMBER OF SEARCH STATES IN PREVIOUS PERIOD (N) : ');
    READLN(NMAX);
    WRITELN;
    WRITE('ENTER NUMBER OF SEARCH STATES IN PRESENT PERIOD (X) : ');
    READLN(XMAX);
    WRITELN;
    WRITE('INCLUDE UP/DOWN TIME CONSTRAINTS (Y OR N) : ');
    READLN(INCLUDE);
    WRITELN;
    IF (INCLUDE <> 'Y') AND (INCLUDE <> 'y') THEN
      BEGIN
      FOR J := 1 TO NUMUNT DO BEGIN
        UNTUPMIN[ J ] := 0;
        UNTDOWNMIN[ J ] := 0;
      END;
    END;

QUIT:

END;   { end of data input }

{----------------------------------------------------------------------------}
{ <f> <s>   Datadump Procedure}

PROCEDURE DATADUMP( VAR  OUTFILE : TEXT );

VAR I : INTEGER;

BEGIN

    WRITELN(OUTFILE);
    WRITELN(OUTFILE, ' DATA FILE : ',FILENAME);
    WRITELN(OUTFILE);
    WRITELN(OUTFILE, TITLE1);
    WRITELN(OUTFILE, TITLE2);
    WRITELN(OUTFILE);
    WRITELN(OUTFILE,'UNIT DATA');
    WRITELN(OUTFILE);
    WRITE(OUTFILE,'UNIT  MIN  MAX   INC   NO LOAD ');
    WRITELN(OUTFILE,'START  FUEL  MIN UP  MIN DOWN  INIT');
    WRITE(OUTFILE,'      MW   MW     HR    COST    ');
    WRITELN(OUTFILE,'COST  COST  PERIODS PERIODS   STATUS');
    FOR I := 1 TO NUMUNT DO
      BEGIN
      WRITE(OUTFILE,I:4,' ');
      WRITE(OUTFILE,UNTMIN[I]:4:0,' ');
      WRITE(OUTFILE,UNTMAX[I]:4:0,' ');
      WRITE(OUTFILE,UNTINC[I]:6:0,' ');
      WRITE(OUTFILE,UNTNOLOADCOST[I]:6:0,'   ');
      WRITE(OUTFILE,UNTSTARTCOST[I]:5:0,' ');
      WRITE(OUTFILE,UNTFUELCOST[I]:3:1,'    ');
      WRITE(OUTFILE,UNTUPMIN[I]:3,'    ');
      WRITE(OUTFILE,UNTDOWNMIN[I]:4,'      ');
      WRITELN(OUTFILE,UNTSTATINI[I]:4);
    END; { I }
    WRITELN(OUTFILE);
    WRITELN(OUTFILE,'LOAD DATA DURING PERIODS OF ',PERIOD_LENGTH:1:3,' HOURS');
    WRITELN(OUTFILE);
    WRITELN(OUTFILE,'PERIOD    LOAD');
    WRITELN(OUTFILE,'           MW');
    FOR I :=1 TO NUMPER DO
    BEGIN
      WRITELN(OUTFILE,I:4,'   ',PERIOD_DATA[I].SYSLOAD:9:3);
    END; { I }

    WRITELN(OUTFILE);
    IF ORDERTYPE = 1 THEN WRITELN(OUTFILE, ' PRIORITY ORDER ')
                     ELSE WRITELN(OUTFILE, ' COMPLETE ENUMERATION ');

    WRITELN(OUTFILE);
    WRITELN(OUTFILE,'NUMBER OF SEARCH STATES PREVIOUS PERIOD = ',NMAX:4);
    WRITELN(OUTFILE);
    WRITELN(OUTFILE,'NUMBER OF SEARCH STATES PRESENT PERIOD = ',NMAX:4);
    WRITELN(OUTFILE);
    IF (INCLUDE = 'Y') OR (INCLUDE = 'y') THEN
        WRITELN(OUTFILE, ' MIN UP/DOWN CONSTRAINTS ARE INCLUDED')
        ELSE
        WRITELN(OUTFILE, ' MIN UP/DOWN CONSTRAINTS ARE NOT INCLUDED');
    WRITELN(OUTFILE);

END; { end datadump procedure }

{----------------------------------------------------------------------------}
{ <f> <s>   Procedure statelist  }

PROCEDURE STATE_LIST( VAR  OUTFILE : TEXT );

VAR I,J : INTEGER;

BEGIN

    WRITELN(OUTFILE);
    WRITELN(OUTFILE,'UNIT STATUS TABLE USED IN DYNAMIC PROGRAMMING SEARCH');
    WRITELN(OUTFILE);
    WRITELN(OUTFILE,'STATE  UNIT STATUS');
    WRITE(OUTFILE,'     ');
    FOR J := 1 TO NUMUNT DO WRITE(OUTFILE,J:4);
    WRITELN(OUTFILE);
    FOR J := 1 TO 7+NUMUNT*4 DO WRITE(OUTFILE,'-');
    WRITELN(OUTFILE);
    FOR I := 1 TO NUMSTAT DO BEGIN
      WRITE(OUTFILE,I:4,'   ');
      FOR J := 1 TO NUMUNT DO BEGIN
        IF (J IN UNTSTAT[ I ]) THEN
          WRITE(OUTFILE,'ON  ')
        ELSE
          WRITE(OUTFILE,'OFF ');
      END; { J }
      WRITELN(OUTFILE);
    END; { I }

END;

{----------------------------------------------------------------------------}
{ <f> <s>   Procedure FINAL_OUTPUT  }

PROCEDURE FINAL_OUTPUT( VAR  OUTFILE : TEXT );

VAR I,J : INTEGER;

BEGIN

      
      WRITELN(OUTFILE);
      OPTCOST := INFINITY;
      OPTSTATE := 0;
      FOR I := 1 TO NUMSTAT DO WITH PERIOD_DATA[NUMPER] DO BEGIN
       IF (FCOST[ I ] <= OPTCOST) THEN BEGIN
         {                       }
         { New optimum end point }
         {                       }
         OPTCOST := FCOST[ I ];
         OPTSTATE := I;
       END;
      END; { I }
      WRITELN(OUTFILE,'OPTIMUM COMMITMENT SCHEDULE ');
      WRITELN(OUTFILE);
      WRITELN(OUTFILE,'TOTAL COST = ',OPTCOST:1:2,' R');
      WRITELN(OUTFILE);
      WRITE(OUTFILE,'PERIOD STATE    UNIT STATUS ');
      FOR I:=1 TO NUMUNT*4-11 DO WRITE(OUTFILE,' ');
      WRITELN(OUTFILE,' PCOST     LOAD');
      WRITE(OUTFILE,'            ');
      FOR J := 1 TO NUMUNT DO WRITE(OUTFILE,J:4);
      WRITELN(OUTFILE,'       R/HR      MW');
      FOR J := 1 TO 34+NUMUNT*4 DO WRITE(OUTFILE,'-');
      WRITELN(OUTFILE);
      FOR K := NUMPER DOWNTO 1 DO WITH PERIOD_DATA[K] DO BEGIN
        WRITE(OUTFILE,K:4,'    ',OPTSTATE:3,'   ');
        FOR J := 1 TO NUMUNT DO
          IF (J IN UNTSTAT[ OPTSTATE ]) THEN
            WRITE(OUTFILE,'ON  ')
          ELSE
            WRITE(OUTFILE,'OFF ');
        WRITE(OUTFILE,'  ');
        WRITE(OUTFILE,PCOST[ OPTSTATE ]:7:0,'   ');
        WRITELN(OUTFILE,SYSLOAD:8:3);
        OPTSTATE := PATH[ OPTSTATE ];
      END; { M }

END;


{----------------------------------------------------------------------------}
{ <f> <s>   Setstate Procedure}
 

PROCEDURE SETSTATE(VAR STATE:SET_OF_UNIT_NUMBERS;
                         UNTSTAT:UNIT_ARRAY_INTEGER);
{ ------------------------------------------------------------------- }
{                                                                     }
{ SUBROUTINE TO CONVERT UNIT STATUS TO SET VARIABLE                   }
{                                                                     }
{                                                                     }
  VAR
      I:INTEGER;
  BEGIN
    STATE:=[];
    FOR I:=1 TO NUMUNT DO IF (UNTSTAT[ I ] > 0) THEN STATE:=STATE+[I];
  END;
{                                                                     }
{                                                                     }
{----------------------------------------------------------------------------}
{ <f> <s>   Economic Dispatch Procedure }
 PROCEDURE EDC;
{ ------------------------------------------------------------------- }
{                                                                     }
{ SUBROUTINE TO PERFORM ECONOMIC DISPATCH OF UNITS FOR PERIOD 'K'     }
{                                                                     }
{ RETURNS PCOST FOR PERIOD K                                          }
{                                                                     }
  VAR
      I,J:INTEGER;
      MINUNT:INTEGER;
      STOP:BOOLEAN;
      SUMMAX,SUMMIN:REAL;
      MININC:REAL;
      UNTCOST,DISPLOAD:REAL;
      UNTRANGE:REAL;
  BEGIN
    WITH PERIOD_DATA[K] DO FOR I := 1 TO NUMSTAT DO BEGIN
      SUMMIN := 0.0;
      SUMMAX := 0.0;
      PCOST[ I ] := 0.0;
      FOR J := 1 TO NUMUNT DO BEGIN
        IF (J IN UNTSTAT[ I ]) THEN BEGIN
          SUMMIN := SUMMIN + UNTMIN[ J ];
          SUMMAX := SUMMAX + UNTMAX[ J ];
        END
      END; { J }
      IF (SUMMIN >= SYSLOAD) OR (SYSLOAD >= SUMMAX) THEN
        {                                                              }
        { Failure of the above test means that the state is infeasible }
        { so we set the cost to infinity and do not dispatch.          }
        {                                                              }
        PCOST[ I ] := INFINITY
      ELSE BEGIN
        {                     }
        { Begin unit dispatch }
        {                     }
        DISPLOAD := SYSLOAD - SUMMIN;
        {                                 }
        { Set all units to min generation }
        {                                 }
        FOR J := 1 TO NUMUNT DO IF (J IN UNTSTAT[ I ])
        THEN UNTGEN[ J ] := UNTMIN[ J ];
        {                               }
        { Find unit with least inc cost }
        {                               }
        REPEAT
          MININC := INFINITY;
          MINUNT := 0;
          FOR J := 1 TO NUMUNT DO BEGIN
            IF (J IN UNTSTAT[ I ]) AND (UNTGEN[ J ] = UNTMIN[ J ]) AND
            (UNTINC[ J ] < MININC) THEN BEGIN
              MININC := UNTINC[J];
              MINUNT := J;
            END;
          END;
          UNTRANGE := UNTMAX[ MINUNT ] - UNTMIN[ MINUNT ];
          STOP := (DISPLOAD < UNTRANGE);
          IF (NOT STOP) THEN BEGIN
            {                      }
            { Dispatch unit to max }
            {                      }
            UNTGEN[ MINUNT ] := UNTMAX[ MINUNT ];
            DISPLOAD := DISPLOAD - UNTRANGE;
          END;
        UNTIL STOP;
        {                        }
        { Final unit part loaded }
        {                        }
        UNTGEN[ MINUNT ] := UNTMIN[ MINUNT ] + DISPLOAD;
        {                 }
        { Calculate costs }
        {                 }
        FOR J := 1 TO NUMUNT DO BEGIN
          IF (J IN UNTSTAT[ I ]) THEN BEGIN
            UNTCOST := UNTNOLOADCOST[J] + UNTFUELCOST[J]
            * UNTGEN[J]*UNTINC[J]/1000.0;
            UNTCOST := UNTCOST * PERIOD_LENGTH;
            PCOST[I] := PCOST[I] + UNTCOST;
          END;
        END;
      END;
    END; { I }
  END;
{                                                                     }
{                                                                     }
{----------------------------------------------------------------------------}
{ <f> <s>   Unit State Dump Procedure }
 PROCEDURE STATUSDUMP( K:INTEGER; VAR OUTFILE : TEXT);
{ ------------------------------------------------------------------- }
{                                                                     }
{ SUBROUTINE TO DUMP UNIT STATUS AT PERIOD 'K'                        }
{                                                                     }
  VAR
      I,J:INTEGER;

  BEGIN

    IF K = 0 THEN
      BEGIN
      WRITELN(OUTFILE);
      WRITELN(OUTFILE, ' INITIAL CONDITIONS ');
      END
    ELSE
      BEGIN
      WRITELN(OUTFILE);
      WRITELN(OUTFILE,'PERIOD ',K,'   SYSTEM LOAD = ',
              PERIOD_DATA[K].SYSLOAD:1:3,' MW');
      END;

    WITH PERIOD_DATA[K] DO BEGIN
      WRITE(OUTFILE,'STATE  UNIT STATUS ');
      FOR I:=1 TO NUMUNT*4-11 DO WRITE(OUTFILE,' ');
      WRITELN(OUTFILE,' PCOST  PATH    FCOST');
      WRITE(OUTFILE,'     ');
      FOR I:=1 TO NUMUNT DO WRITE(OUTFILE,I:4);
      WRITELN(OUTFILE,'     R/HR            R');
      FOR I := 1 TO 30+NUMUNT*4 DO WRITE(OUTFILE,'-');
      WRITELN(OUTFILE);
      FOR I := 1 TO NUMSTAT DO BEGIN
        {                        }
        { skip infeasible states }
        {                        }
        IF (PCOST[I] <> INFINITY) AND (UNTSTATNOW[ I, 1 ] <> 0) THEN BEGIN
          WRITE(OUTFILE,I:3,'  ');
          FOR J := 1 TO NUMUNT DO WRITE(OUTFILE,UNTSTATNOW[ I, J ]:4);
          WRITE(OUTFILE,'  ');
          WRITE(OUTFILE,PCOST[ I ]:7:0,'  ');
          WRITE(OUTFILE,PATH[ I ]:3,'  ');
          WRITELN(OUTFILE,FCOST[ I ]:9:2);
        END;
      END;
    END;
  END;
{                                                                     }
{                                                                     }
{----------------------------------------------------------------------------}
{ <f> <s>   Order Procedure }
 PROCEDURE ORDER(VAR ORDERTABLE:STATE_ARRAY_REAL;NUMORDER:INTEGER);
{ ------------------------------------------------------------------- }
{                                                                     }
{ SUBROUTINE TO ORDER A LIST, LEAST FIRST                             }
{                                                                     }
{ input NUMORDER = the number of items order                          }
{ input ORDERTABLE = the items to be ordered                          }
{ output ORDERINDEX = pointer to order value table                    }
{                                                                     }
{ NXT = Table used in order subroutine                                }
{                                                                     }
  VAR
      STOP:BOOLEAN;
      I,J,TOP,LAST,INDX:INTEGER;
      NXT:STATE_ARRAY_INTEGER;
  BEGIN
    FOR I := 1 TO NUMORDER DO BEGIN
      IF (I <= 1) THEN BEGIN
        TOP := 1;
        NXT[ 1 ] := 0;
        END
      ELSE BEGIN
        J := TOP;
        LAST := 0;
        REPEAT
          STOP := TRUE;
          IF (ORDERTABLE[ I ] > ORDERTABLE[ J ]) THEN BEGIN
            LAST := J;
            J := NXT[ J ];
            STOP  := (J = 0);
            IF (STOP) THEN BEGIN
              NXT[ LAST ] := I;
              NXT[ I ] := 0;
            END
            END
          ELSE BEGIN
            IF (J <> TOP) THEN BEGIN
              NXT[ LAST ] := I;             { J not = TOP }
              NXT[ I ] := J;
              END
            ELSE BEGIN
              TOP := I;                     { J = TOP }
              NXT[ I ] := J;
            END;
          END;
        UNTIL STOP;
      END;
    END;
    INDX := 1;
    J := TOP;
    REPEAT
      ORDERINDEX[ INDX ] := J;
      J := NXT[ J ];
      INDX := INDX + 1;
    UNTIL (J = 0);
  END;
{                                                                     }
{                                                                     }
{----------------------------------------------------------------------------}
{ <f> <s>   Best States Procedure }
 PROCEDURE BESTSTATES(VAR SETP:STATE_ARRAY_INTEGER;
                       VAR COST:STATE_ARRAY_REAL;
                       VAR LIM:INTEGER; MAX:INTEGER);
{ ---------------------------------------------- }
{                                                }
{ Subroutines puts the top MAX states into SETP  }
{                                                }
  VAR
      DONE:BOOLEAN;
      INDEX:INTEGER;
  BEGIN
    ORDER(COST,NUMSTAT);
    DONE := FALSE;
    LIM := 0;
    WHILE NOT DONE AND (LIM < MAX) DO BEGIN
      INDEX := ORDERINDEX[ LIM+1 ];
      IF (COST[ INDEX ] = INFINITY) THEN
        DONE := TRUE
      ELSE BEGIN
        LIM := LIM + 1;
        SETP[ LIM ] := INDEX
      END
    END;
  END;
{                                                                     }
{                                                                     }
{----------------------------------------------------------------------------}
{ <f> <s>   Feasibility Test Procedure }
 PROCEDURE FEAS;
{ ------------------------------------------------------------------- }
{                                                                     }
{ SUBROUTINE TO Test feasibility of transition                        }
{ from UNTSTATLAST[ LSTATE ] to UNTSTAT                               }
{                                                                     }
  VAR
      J:INTEGER;
  BEGIN
    VALID := 1;
    SCOST := 0.0;
    J:=1;
    WHILE (VALID = 1) AND (J <= NUMUNT) DO BEGIN
      IF (UNTSTATLAST[ LSTATE, J ] < 0) THEN
        {                                          }
        { Logic below is for unit down last period }
        {                                          }
        IF (J IN UNTSTAT[ XSTATE ]) THEN
          {                                       }
          { Unit up this period ( down to up )    }
          { TRANSITION - test for min down time   }
          { Note: UNTSTATLAST is the number of    }
          { periods the unit was down, while      }
          { UNTDOWNMIN is min number of hours the }
          { unit must be down.                    }
          {                                       }
          IF (  (-UNTSTATLAST[LSTATE,J] * PERIOD_LENGTH)
              < UNTDOWNMIN[J]) THEN
            {                           }
            { Failed min down time test }
            {                           }
            VALID := 0
          ELSE BEGIN
            {                                  }
            { Passed min down test, start unit }
            {                                  }
            UNTSTATTEMP[J] := 1;
            SCOST := SCOST + UNTSTARTCOST[J];
            END
        ELSE
          {                                               }
          { Unit down this period ( stays down )          }
          { NO TRANSITION - increase time down 1 period   }
          {                                               }
          UNTSTATTEMP[ J ] := UNTSTATLAST[ LSTATE, J ] - 1
      ELSE
        {                                        }
        { Logic below is for unit up last period }
        {                                        }
        IF (J IN UNTSTAT[ XSTATE]) THEN
          {                                           }
          { Unit up this period ( up to up )          }
          { NO TRANSITION - increase time up 1 period }
          {                                           }
          UNTSTATTEMP[ J ] := UNTSTATLAST[ LSTATE, J ] + 1
        ELSE
          {                                      }
          { Unit down this period ( up to down ) }
          { TRANSITION - test for min up time    }
          { Note: UNTSTATLAST is the number of    }
          { periods the unit was up, while      }
          { UNTUPMIN is min number of hours the }
          { unit must be up.                    }
          {                                      }
          IF ( (UNTSTATLAST[LSTATE,J] * PERIOD_LENGTH )
                   < UNTUPMIN[J]) THEN
            {                         }
            { Failed min up time test }
            {                         }
            VALID := 0
          ELSE
            {                                         }
            { Passed min up time test, shut down unit }
            {                                         }
            UNTSTATTEMP[J] := -1;
      J:=J+1;
    END; { J }
  END;
{---------------------------------------------------------------------------}
{ <f> <s>   Main Program }
BEGIN
  REPEAT

  DATAINPUT;
         IF IOERR THEN GOTO QUIT;

  IF PRINT_OUTPUT THEN DATADUMP(LST)
                  ELSE DATADUMP(OUTPUT);

    {                          }
    { Build unit status tables }
    {                          }
    IF (ORDERTYPE = 1) THEN BEGIN
      {                           }
      { Build priority order list }
      {                           }
      NUMSTAT := NUMUNT;
      FOR I := 1 TO NUMSTAT DO UNTSTAT[ I ] := [];
      {                                       }
      { Calculate full load ave cost for each }
      { unit and order units.                 }
      {                                       }
      FOR J := 1 TO NUMUNT DO BEGIN
        UNTCOST := UNTNOLOADCOST[J] + UNTFUELCOST[J] *
        UNTMAX[J]*UNTINC[J] / 1000.0;
        UNTFULLAVECOST[ J ] := UNTCOST / UNTMAX[J];
      END; { J }
      {                                       }
      { Call ordering subroutine, returns     }
      { table ORDERINDEX(I)=index to Ith unit }
      {                                       }
      ORDER(UNTFULLAVECOST,NUMSTAT);
      STATE:=[];
      FOR I := 1 TO NUMSTAT DO BEGIN
        STATE := STATE + [ORDERINDEX[ I ]];
        UNTSTAT[ I ] := STATE;
      END; { I }
      END
    ELSE BEGIN
      {                                 }
      { Build complete enumeration list }
      {                                 }
      STATE := [];
      FOR I:=1 TO NUMUNT DO STATE := STATE + [I];
      I := 0;
      WHILE (STATE <> []) DO BEGIN
        I := I+1;
        UNTSTAT[ I ] := STATE;
        BORROW := TRUE;
        J := NUMUNT;
        WHILE BORROW DO
          IF (J IN STATE) THEN BEGIN
            STATE := STATE - [J];
            BORROW := FALSE
            END
          ELSE BEGIN
            STATE := STATE + [J];
            J := J - 1
          END;
      END;
      NUMSTAT := I;
    END;
    {                                       }
    { Search list to find match for initial }
    { state, if not found add state         }
    {                                       }
    SETSTATE(STATE,UNTSTATINI);
    I:=1;
    WHILE (STATE <> UNTSTAT[I]) AND (I < NUMSTAT) DO I:=I+1;
    IF (STATE = UNTSTAT[I]) THEN
      {             }
      { Match found }
      {             }
      INITSTAT:=I
    ELSE BEGIN
      {                                         }
      { No match found, add state to match init }
      {                                         }
      NUMSTAT := NUMSTAT + 1;
      INITSTAT := NUMSTAT;
      IF PRINT_OUTPUT THEN
      WRITELN(LST, 'INITIAL STATE NOT IN PRIORITY LIST, ADDING STATE TO LIST')
      ELSE
      WRITELN(OUTPUT,
       'INITIAL STATE NOT IN PRIORITY LIST, ADDING STATE TO LIST');
      
      {                                   }
      { Store init state so it is in list }
      {                                   }
      UNTSTAT[ INITSTAT ] := STATE;
    END;
    {                         }
    { Print unit status table }
    {                         }
    IF PRINT_OUTPUT THEN STATE_LIST(LST)
                    ELSE STATE_LIST(OUTPUT);
    {                                     }
    { LIMIT SEARCH STATES TO BE LESS THAN }
    { OR EQUAL TO THE NUMBER OF STATES    }
    {                                     }
    IF (NMAX > NUMSTAT) THEN NMAX := NUMSTAT;
    IF (XMAX > NUMSTAT) THEN XMAX := NUMSTAT;
    {                                     }
    { Load FCOST and UNTSTATNOW tables to }
    { reflect initial conditions. Also    }
    { initialize PATH AND PCOST for       }
    { initial conditions.                 }
    {                                     }
    WITH PERIOD_DATA[0] DO BEGIN
      FOR I := 1 TO NUMSTAT DO BEGIN
        FCOST[ I ] := INFINITY;
        FOR J := 1 TO NUMUNT DO UNTSTATNOW[ I, J ] := 0;
      END; { I }
      FCOST[ INITSTAT ] := 0.0;
      PCOST[ INITSTAT ] := 0.0;
      PATH[ INITSTAT ] := 0;
      UNTSTATNOW[ INITSTAT ] := UNTSTATINI;
    END;
    {                                }
    { Print initial conditions       }
    {                                }
    IF PRINT_OUTPUT THEN STATUSDUMP(0,LST)
                    ELSE STATUSDUMP(0,OUTPUT);
    {                                      }
    { Top of main dynamic programming loop }
    {                                      }
    CONTINUE := TRUE;
    K := 1;
    WHILE (K <= NUMPER) AND CONTINUE DO WITH PERIOD_DATA[K] DO BEGIN
      {                                       }
      { Store UNTSTATLAST from present status }
      {                                       }
      UNTSTATLAST := UNTSTATNOW;
      FOR I := 1 TO NUMSTAT DO BEGIN
        FCOST[ I ] := INFINITY;
        PATH[ I ] := 0;
        FOR J := 1 TO NUMUNT DO UNTSTATNOW[ I, J ] := 0;
      END; { I }
      {                                           }
      { Build SETL, list of states in last period }
      {                                           }
      IF (K = 1) THEN BEGIN
        NLIM := 1;
        SETL[ 1 ] := INITSTAT;
        END
      ELSE
        {                                                }
        { Get top NMAX states in SETL                    }
        {                                                }
        BESTSTATES(SETL,PERIOD_DATA[ K-1 ].FCOST,NLIM,NMAX);
      {                                        }
      { Build PCOST for all states at period K }
      {                                        }
      EDC;
      {                                       }
      { Build SETX, list of states in present }
      {                                       }
      BESTSTATES(SETX,PCOST,XLIM,XMAX);
      {                                    }
      { Search all transitions from states }
      { in SETL to states in SETX          }
      {                                    }
      CONTINUE := FALSE;
      FOR X := 1 TO XLIM DO BEGIN
        XSTATE := SETX[ X ];
        FOR N := 1 TO NLIM DO BEGIN
          LSTATE := SETL[ N ];
          FEAS;
          IF (VALID = 1) THEN BEGIN
            {                                         }
            { Valid transtion, see if cost is minimum }
            {                                         }
            PATHCOST := PERIOD_DATA[ K-1].FCOST[ LSTATE ] + SCOST +
                           PCOST[ XSTATE ];
            IF (PATHCOST <= FCOST[ XSTATE ]) THEN BEGIN
              {                             }
              { New minimum cost path found }
              {                             }
              FCOST[ XSTATE ] := PATHCOST;
              UNTSTATNOW[ XSTATE ] := UNTSTATTEMP;
              PATH[ XSTATE ] := LSTATE;
              CONTINUE := TRUE;
            END;
          END;
        END; { N }
      END; { X }
      {                                     }
      { Done with all paths for this period }
      { Print results for current period    }
      {                                     }
      IF PRINT_OUTPUT THEN STATUSDUMP(K,LST)
                      ELSE STATUSDUMP(K,OUTPUT);
      K := K + 1;
    END; { K }
    {                  }
    { Printout routine }
    {                  }
    IF CONTINUE THEN BEGIN 
      IF PRINT_OUTPUT THEN FINAL_OUTPUT(LST)
                      ELSE FINAL_OUTPUT(OUTPUT);
      END
    ELSE
      IF PRINT_OUTPUT THEN  WRITELN(LST,'THERE IS NO SOLUTION')
                      ELSE  WRITELN(OUTPUT,'THERE IS NO SOLUTION');

    QUIT:

    WRITELN;
    WRITE('DO YOU WANT TO RUN UNITCOM AGAIN? (Y OR N) : ');
    READLN(QUITFLAG);
  UNTIL (QUITFLAG <> 'Y') AND (QUITFLAG <> 'y');
{ ------------------------------------------------------------------- }
END.

