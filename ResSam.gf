resource ResSam = open Prelude in {

flags
  coding=utf8 ;

param
  Number = Sg | Du | Pl;
  Case   = Nom | Acc | Ill | Lok | Kom ;
  Agr    = Ag Number Person ;
  TTense = TPres | TPerf | TPast | TFut ;
  Person = Per1 | Per2 | Per3 ;

 -- VNeg is the form used after the negation verb in present tense.
  VForm = VInf | VPres Agr | VPast Agr | VPart | VNeg | VSup;
  
  -- APred: the car is red, AAttr: the car has red seats
  AForm = APred | AAttr ; 

  ClForm = ClDir | ClInv ;
  QForm = QDir | QIndir ;
  
  -- Saami inflects verbs and nouns in these three categories, this cannot really
  -- be implemented through a smart paradigm and must be given in lexicon.
  -- verbs under ROdd can only end in "it"
  -- Contract are "joined words" that form a noun or a verb
  RInflectPar = REven | ROdd | RContract ;



oper
  
  VP = {
    verb  : AgrVerb ; 
    compl : Agr => Str ;
    } ;

  NP = {
    s : Case => Str ;
    a : Agr
    } ; 


  AgrVerb : Type = {
    s : ClForm => TTense => Bool => Agr => {fin,inf : Str} ;
    inf : Str
    } ;

  copula : Verb =  {
    s = table {
       VInf => "leat" ; -- | "leakhit" ; -- copula VInf can be two different 
                                         -- words, but compilation takes too long
       VPres (Ag Sg Per1) => "lean" ;
       VPres (Ag Sg Per3) => "lea"  ;
       VPres (Ag Du Per1) => "letne" ;
       VPres (Ag Du Per2) => "leahppi" ;
       VPres (Ag Du Per3) => "leaba" ;
       VPres (Ag Pl Per2) => "lehpet"  ;
       VPres _          => "leat" ; 
       VPast (Ag Sg Per1) => "ledjen" ;
       VPast (Ag Sg Per2) => "ledjet" ;
       VPast (Ag Sg Per3) => "lei" ;
       VPast (Ag Du Per1) => "leimme" ;
       VPast (Ag Du Per2) => "leidde" ;
       VPast (Ag Du Per3) => "leigga" ;
       VPast (Ag Pl Per1) => "leimmet" ;
       VPast (Ag Pl Per2) => "leiddet" ;
       VPast (Ag Pl Per3) => "leidje" ;
       VPart              => "lean" ;
       VSup               => "leamaš" ;
       VNeg               => "leat" 
       }
    } ;
  
  -- verb for expressing futurum
  galgat : Verb = mkVerbEven "galgat" "galgg" ;
    
   agrV : Verb -> AgrVerb = \v -> {
   
   s = \\d,t,p,a => case <t,p> of {
      <TPast,True>  => {fin = v.s ! VPast a          ; inf = ""} ;
      <TPast,False> => {fin = negation.s ! TPast ! a ; inf = v.s ! VPart } ;
      <TPerf,True>  => {fin = copula.s ! VPres a     ; inf  = v.s ! VPart } ;
      <TPerf,False> => {fin = negation.s ! TPast ! a ; inf = copula.s ! VNeg ++ v.s ! VPart } ;
      <TPres,True>  => {fin = v.s ! VPres a          ; inf = ""} ;                  
      <TPres,False> => {fin = negation.s ! TPres ! a ; inf = v.s ! VNeg } ;
      <TFut ,True>  => {fin = galgat.s ! VPres a     ; inf = v.s ! VInf } ;                  
      <TFut ,False> => {fin = negation.s ! TPres ! a ; inf = galgat.s ! VNeg ++ v.s ! VInf }      
      };
    inf = v.s ! VInf;
     };
    
    
    -- negation verb
  negation : {s : TTense => Agr => Str} = { 
    s = \\t,a => case <t,a> of {
       <TPerf,_     > => nonExist ;
       <TFut, _     > => nonExist ;
       <_,Ag Sg Per1> => "in"  ;
       <_,Ag Sg Per2> => "it"  ;
       <_,Ag Sg Per3> => "ii"  ;
       <_,Ag Du Per1> => "ean" ;
       <_,Ag Du Per2> => "eahppi" ;
       <_,Ag Du Per3> => "eaba"   ; 
       <_,Ag Pl Per1> => "eat"    ;
       <_,Ag Pl Per2> => "ehpet"  ;
       <_,Ag Pl Per3> => "eai"   
       }
    } ;

   infVP : Agr -> VP -> Str = \a,vp -> 
     vp.verb.inf ++ vp.compl ! a; 
	
  neg : Bool -> Str = \b -> case b of {True => [] ; False => "not"} ;


  conjAgr : Number -> Agr -> Agr -> Agr = \n,xa,ya -> 
    case <xa,ya> of {
       <Ag xn xp, Ag yn yp> => 
        Ag (conjNumber xn yn n) (conjPerson xp yp)
      } ;

  conjNumber : Number -> Number -> Number -> Number = \m,n,c ->
    case <m,n,c> of {
       <Sg,Sg,Pl> => Du ;
       <_,_,Pl  > => Pl ;
       <Pl,_,_   > => Pl ;
       <_,Pl,_   > => Pl ;
       <Du,_,_   > => Du ;
       <_,_,_    > => n 
    };
    
  conjPerson : Person -> Person -> Person = \p,q ->
    case <p,q> of {
      <Per1,_> | <_,Per1> => Per1 ;
      <Per2,_> | <_,Per2> => Per2 ;
      _                   => Per3
      } ;


  Noun : Type = {s : Number => Case => Str } ;
  Adj  : Type = {s : AForm => Number => Str } ; 
  Verb : Type = {s : VForm =>  Str };
  Det  : Type = {s : Case => Str ; n : Number} ;
  

  regNoun : Str -> RInflectPar -> Noun = \s,i -> 
    mkNoun s s i ;


  mkNoun : Str -> Str -> RInflectPar -> {s : Number => Case => Str} = 
     \muorra,muora,i -> case <i,last muorra> of {
                          <ROdd,_>         => mkNounOdd   muorra muora ;
                          <Even,("s"|"t")> => mkNounEvenT muorra  ;
                          _                => mkNounEven  muorra muora i 
                        };

   mkNounOdd : Str -> Str -> {s : Number => Case => Str} = \beana,beatnaga -> 
    let beatnag = Predef.tk 1 beatnaga in {
    s = table { Sg => table { Nom => beana ;
                              Acc => beatnaga ;
                              Lok => beatnag + "is" ;
                              Kom => difftongChange (beatnag + "iin") ;
                              Ill => difftongChange (beatnag + "ii") 
                            };
                _ => table { Nom => beatnaga + "t" ;
                             Acc => difftongChange (beatnag + "iid") ;
                             Lok => difftongChange (beatnag + "iin") ;
                             Kom => difftongChange (beatnag + "iiguin") ;
                             Ill => difftongChange (beatnag + "iidda" )
                           }
              }             
    } ;
    
    
   -- for Even and Contracted nouns 
   mkNounEven : Str -> Str -> RInflectPar -> {s : Number => Case => Str} = \muorra,muora,i -> {
     s = table { Sg => table {Nom => muorra ;
                             Acc => muora  ;
                             Lok => muora + "s" ;
                             Kom => difftongChange (muora + "in") ;
                             Ill => case i of {REven     => mkIllA muorra ; --difftongChange (muorra + "i") ;
                                               _          => difftongChange muora}        
                                                   -- may be Contract, but never Odd               
                            };
                _ => mkEvenPl muora 
              }             
    } ;
    
    mkIllA : Str -> Str = \muorra -> case last muorra of { "a" => difftongChange (init muorra + "ii"); _ => difftongChange (muorra + "i")};
    
    mkNounEvenT : Str ->  {s : Number => Case => Str} = \lavvordat-> {
     s = let
      const = consonantChange (last lavvordat) ; 
      lavvordaga  = init lavvordat + const.fst + "a";
      lavvordahk  = init lavvordat + const.snd + "a"
      in
     table { Sg => table {Nom => lavvordat;
                          Acc =>  lavvordaga  ;
                          Lok =>  lavvordaga  + "s" ;
                          Kom =>  difftongChange (lavvordaga + "in") ;
                          Ill =>   difftongChange(lavvordahk  + "ii")        
                            };
                _  => mkEvenPl lavvordaga 
              }             
    } ; 
    
   mkEvenPl : Str -> Case => Str = \muora -> 
   table { Nom => muora + "t" ;
           Acc => difftongChange (muora + "id") ;
           Lok => difftongChange (muora + "in") ;
           Kom => difftongChange (muora + "iguin") ;
           Ill => difftongChange (muora + "ide" )
                            } ;

  regAdj : Str -> Adj = \a -> mkAdj1 a a ;

  mkAdj1 : Str -> Str -> Adj = \n,a -> 
      case last n of {
          (#vowel) => mkAdj2 n (n+"t") a;
          _        => mkAdj2 n (n+"at") a
      } ;


  mkAdj2 : Str -> Str -> Str -> Adj = \ns,np,a -> {
    s = table {
        APred => table { Sg => ns; _ => np } ;
        AAttr => \\_ => a 
        }
    };
  


 VerbEnds : Type = { a1 : Str ; a2 : Str ; e : Str ; i : Str  } ;
 itEnds : VerbEnds = {a1 = "á"; a2 = "á"; e = "e"; i = "i"} ;
 atEnds : VerbEnds = {a1 = "a"; a2 = "á"; e = "e"; i = "a"} ;
 utEnds : VerbEnds = {a1 = "u"; a2 = "u"; e = "o"; i = "u"} ;
 etEnds : VerbEnds = {a1 = "e"; a2 = "e"; e = "e"; i = "i"} ;
 otEnds : VerbEnds = {a1 = "o"; a2 = "o"; e = "o"; i = "u"} ;
 a'tEnds : VerbEnds = {a1 = "á"; a2 = "á"; e = "á"; i = "á"} ;

  mkVV : Str -> Str -> AgrVerb = \x,y ->
    agrV (mkVerbEven x  y);
  

  regVerb : Str -> RInflectPar -> Verb = \vb,i -> 
  let mkVerb  = case i of {REven => mkVerbEven; _ => mkVerbItOdd};
      v = Predef.tk 2 vb ;
  in mkVerb vb v;
  
  mkVerb : (_,_ : Str) -> RInflectPar -> Verb = \boahtit,boad,i -> 
  case i of {
  	REven => mkVerbEven  boahtit boad ;
  	_     => mkVerbItOdd boahtit boad 
  };
  
  mkVerbEven : (_,_ : Str) -> Verb = \boahtit,boad -> 
   case Predef.dp 2 boahtit of {
      "it" => mkVerbAtIt boahtit boad itEnds ;
      "at" => mkVerbAtIt boahtit boad atEnds ;
      "et" => mkVerbEt   boahtit boad etEnds;
      "ut" => mkVerbAtIt boahtit boad utEnds ;
      "át" => mkVerbEt boahtit boad a'tEnds;
      "ot" => mkVerbEt boahtit boad otEnds 
    };
    
  mkVerbAtIt : (_,_: Str) -> VerbEnds -> Verb = \boahtit,boad,ends-> 
    let 
       boaht  = Predef.tk 2 boahtit ;
       a      = case ends.a2 of {"u" => "o"; _ => ends.a2}
    in {
	    s = table {
		  VInf  => boahtit ;
		  VNeg  => boad+ends.e ;
		  (VPres ag) => mkPresAtIt boaht boad ag ends ;
		  (VPast ag) => mkPastAtIt boaht boad ag ends ;
		  VPart      => boaht + a + "n" ;
		  VSup       => boad  + a + "žit"
		  } 
    } ;

  mkVerbEt : (_,_ : Str) -> VerbEnds -> Verb = \fertet,fert2,ends -> 
    let 
       fert1 = Predef.tk 2 fertet 
    in {
	    s = table {
		  VInf  => fertet ;
		  VNeg  => fert2 + ends.e ;
		  (VPres ag) => mkPresEt fert1 fert2 ag ends ;
		  (VPast ag) => mkPastEt fert1 fert2 ag ends ;
		  VPart      => difftongChange ( fert1 + ends.e +"n" ) ;
		  VSup       => fert1 + ends.e + "žit"
		  } ;
    } ;

  mkVerbItOdd : (_,_: Str) -> Verb = \rahkistit,rahkist-> 
    { s = table {
		  VInf  => rahkistit ;
		  VNeg  => Predef.tk 3 rahkistit ;
		  (VPres ag) => mkPresIt1 (Predef.tk 2 rahkistit) rahkist ag ;
		  (VPast ag) => mkPastIt1 (Predef.tk 2 rahkistit)  rahkist ag ;
		  VPart      => (Predef.tk 2 rahkistit) + "an" ;
		  VSup       => difftongChange ((Predef.tk 2 rahkistit) + "eažžat" )
		  } ;
    } ;

  mkPresAtIt : (_,_: Str) -> Agr -> VerbEnds -> Str =
     \boaht,boad,agr,ends -> 
     let a1 = ends.a1 ; a2 = ends.a2; e = ends.e; i = ends.i in
      case agr of {
	    Ag Sg Per1 => boad + a1 + "n" ;
		Ag Sg Per2 => boad + a1 + "t" ;
		Ag Sg Per3 => boaht + a2 ;
		Ag Du Per1 => difftongChange (boaht + e ) ;
		Ag Du Per2 => difftongChange (boaht + i + "beahtti" ) ;
		Ag Du Per3 => difftongChange (boaht + i + "ba") ; 
		Ag Pl Per1 => difftongChange (boaht + i + "t") ;
		Ag Pl Per2 => difftongChange (boaht + i + "behtet")  ;
		Ag Pl Per3 => difftongChange (boaht + e + "t")
     } ;

    mkPastAtIt : ( _,_ : Str) -> Agr -> VerbEnds -> Str =
     \geahcc,geahc,agr,ends -> 
      let e = ends.e ; a = ends.i  in  
      case agr of {
	    Ag Sg Per1 => difftongChange (geahcc + e + "n")  ; 
		Ag Sg Per2 => difftongChange (geahcc + e + "t" ) ; 
		Ag Sg Per3 => difftongChange (geahc  + a + "i" ) ;
	    Ag Du Per1 => difftongChange (geahc  + a + "ime" );
		Ag Du Per2 => difftongChange (geahc  + a + "ide" );
		Ag Du Per3 => difftongChange (geahc  + a + "iga" ); 
		Ag Pl Per1 => difftongChange (geahc  + a + "imet" )  ;
		Ag Pl Per2 => difftongChange (geahc  + a +"idet" ) ;
		Ag Pl Per3 => difftongChange (geahcc + e) 
     } ;


    mkPresEt : (_,_: Str) -> Agr -> VerbEnds -> Str =
     \fert1,fert2,agr,ends -> 
     let e = ends.a1 in
      case agr of {
	    Ag Sg Per1 => difftongChange (fert2 + e + "n") ;
		Ag Sg Per2 => difftongChange (fert2 + e +"t" );
		Ag Sg Per3 => difftongChange (fert1 + e ) ;
		Ag Du Per1 => difftongChange (fert1 + e +"jetne") ;
		Ag Du Per2 => difftongChange (fert1 + e +"beahtti") ;
		Ag Du Per3 => difftongChange (fert1 + e +"ba") ; 
		Ag Pl Per1 => difftongChange (fert1 + e +"t") ;
		Ag Pl Per2 => difftongChange (fert1 + e +"behtet")  ;
		Ag Pl Per3 => difftongChange (fert1 + e +"jit" )
     } ;


    mkPastEt : (_,_: Str) -> Agr -> VerbEnds -> Str =
     \fert1,fert2,agr,ends -> 
     let e = ends.a1 ; i = ends.i in
       case agr of {
	        Ag Sg Per1 => difftongChange (fert1 + e + "jin") ;
		    Ag Sg Per2 => difftongChange (fert1 + e +"jit")  ;
		    Ag Sg Per3 => difftongChange (fert2  + i + "i" ) ;
	        Ag Du Per1 => difftongChange (fert2  + i + "ime") ;
		    Ag Du Per2 => difftongChange (fert2 +  i + "ide" );
		    Ag Du Per3 => difftongChange (fert2 +  i + "iga") ; 
		    Ag Pl Per1 => difftongChange (fert2 +  i + "imet") ;
		    Ag Pl Per2 => difftongChange (fert2 + i + "idet") ;
		    Ag Pl Per3 => difftongChange (fert1 + e +"je" )
     } ; 

   mkPresIt1 : (_,_: Str) -> Agr -> Str =
     \rahkist1, rahkist2, agr -> 
      case agr of {
	        Ag Sg Per1 => rahkist1 + "an" ;
		Ag Sg Per2 => rahkist1 + "at" ;
		Ag Sg Per3 => rahkist1 + "a"  ;
		Ag Du Per1 => difftongChange (rahkist1 + "etne") ;
		Ag Du Per2 => difftongChange (rahkist1 + "eahppi") ;
		Ag Du Per3 => difftongChange (rahkist1 + "eaba") ; 
		Ag Pl Per1 => rahkist1 + "at" ;
		Ag Pl Per2 => difftongChange (rahkist1 + "ehpet")  ;
		Ag Pl Per3 => difftongChange (rahkist1 + "it")
     } ;



    mkPastIt1 : (_,_: Str) -> Agr -> Str =
     \rahkist1,rahkist2,agr -> 
       case agr of {
	    Ag Sg Per1 => difftongChange (rahkist1 + "in" ) ;
		Ag Sg Per2 => difftongChange (rahkist1 + "it" ) ;
		Ag Sg Per3 => difftongChange (rahkist1  + "ii")  ;
	    Ag Du Per1 => difftongChange (rahkist1  + "eimme") ;
		Ag Du Per2 => difftongChange (rahkist1  + "eidde") ;
		Ag Du Per3 => difftongChange (rahkist1 + "eigga") ; 
		Ag Pl Per1 => difftongChange (rahkist1 + "eimmet")   ;
		Ag Pl Per2 => difftongChange (rahkist1 + "eiddet")  ;
		Ag Pl Per3 => difftongChange (rahkist1 + "e")
     } ;  

  mkDet : Str -> Number -> {s : Case => Str ; n : Number } = \s,n ->
     { s = \\_ => s ; n = n } ;

   mkDetCase = overload {
    mkDetCase : (_ : Str) -> Number -> Det 
      = \s,n -> lin Det (mkDetCaseLok "in" s n) ;
    mkDetCase : (_,_ : Str) -> Number -> Det 
      = \l,s,n -> lin Det (mkDetCaseLok l s n ) ;
     } ;
  
  mkDetCaseLok : Str -> Str -> Number -> {s : Case => Str ; n : Number} =  \lokPl,s,n -> 
    let det = init s in
   {
    s = case n of {
        Sg => table { 
            Nom => det + "t";
            Acc => det + "n" ;
            Lok => det + "s" ;
            Ill => det + "sa" ;
            Kom => det + "inna"  
        } ;
        _ => table { 
            Nom => det + "t";
            Acc => det + "id" ;
            Lok => det + lokPl ;
            Ill => det + "idda" ;
            Kom => det + "iguin" 
        }
    } ;
    n = n
  } ;

  refl : Agr => Str =
   table {
           Ag Sg Per1 => "alddán" ;
     	   Ag Du Per1 => "alddáme" ; 
    	   Ag Pl Per1 => "alddámet" ;
           Ag Sg Per2 => "alddát";
    	   Ag Du Per2 => "alddáde"  ;
    	   Ag Pl Per2 => "alddádet" ;  	   
           Ag Sg Per3 => "alddes" ;
           Ag Du Per3 => "alddeska" ;
    	   Ag Pl Per3 => "alddeset" 
     };
   
   
   
  pronNP : (s,a : Str) -> Number -> Person -> NP = 
  \mon,munnje,n,p -> 
    let 
       mu = Predef.take 2 munnje ;
       mun = Predef.take 3 munnje
    in {
    s = case n of {
       Sg => table {
              Nom => mon ;
              Acc => mu ;
              Lok => mu + "s" ;
              Ill => munnje ;
              Kom => mu + "inna" 
             } ;
       Du => table {
              Nom => mon ;
              Acc => mun + "no" ;
              Lok => mun + "nos" ;
              Ill => munnje ;
              Kom => mun + "nuin"
             } ;
       Pl => table {
              Nom => mon ;
              Acc => mu + "n" ;
              Lok => mu + "s" ;
              Ill => munnje ;
              Kom => mu + "nguin"
             }
      } ;
    a = Ag n p
    } ;

   makeIP : Str -> Str -> Number => Case => Str = \gii,gean ->
      let ge = Predef.take 2 gean in 
      table { Sg => table {
                      Nom => gii ;
                      Acc => gean ;
                      Lok => ge + "as" ;
                      Ill => ge + "asa" ;
                      Kom => ge + "ainna"
                    } ;
              _  => table {
                      Nom => ge + "at" ;
                      Acc => ge + "aid" ;
                      Lok => ge + "ain" ;
                      Ill => ge + "aidda" ;
                      Kom => ge + "aiguin"
                    }
             } ;


  -- function for determining whether the input string has an odd or even number
  -- of syllables
  evenOrOdd : Str -> RInflectPar = \s ->
   case s of {
    ((#consonant)*) + (#vowels + #consonants + #vowels + #consonant*)* => REven ;    
    _                                                                  => ROdd 
    };


-- phonological auxiliaries

  difftongChange : Str -> Str = \boahtii ->
    case boahtii of {
        b + oa@("oa" | "ie" | "uo" | "ea") + ht + ii@("ii" | "e" | "o" )  + me
             => b + difftongChange' oa ht + ii + me;
        _    => boahtii 
     } ;

  difftongChange' : Str -> Str -> Str = \oa,ht ->
    case ht of {
       _ + #vowel + _ => oa + ht ;
       _              => Predef.tk 1 oa + ht 
    } ;
    
  consonantChange : Str -> {fst : Str; snd : Str} = \t ->
   case t of {"t" => {fst = "g"; snd = "hk"}; 
              "š" => {fst = "čč"; snd = "žž"};
              "s" => {fst,snd = "s"}};

  vowel    : pattern Str = #("a" | "e" | "i" | "o" | "u" | "á" ) ;
  vowels : pattern Str = #(#vowel + #vowel*) ;
  consonants : pattern Str = #(#consonant + #consonant*) ;
  consonant : pattern Str = #("p"|"f"|"g"|"c"|"r"|"l"|"h"|"d"|"t"|"n"|"ŋ"|"z"
                              |"s"|"q"|"j"|"k"|"b"|"m"|"w"|"v"|"č"|"ž"|"đ");

}
