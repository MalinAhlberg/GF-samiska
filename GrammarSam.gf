concrete GrammarSam of Grammar = open ResSam, Prelude in {
  flags
    coding = utf8 ;
  lincat  
    S  = {s : Str} ;
    Cl = {s : ClForm => TTense => Bool => Str} ; 
    NP = ResSam.NP ;  
    VP = ResSam.VP ;  
    AP = Adj ;
    CN = Noun ;           
    Det = ResSam.Det ;
    N = Noun ;    
    A = Adj ;             
    V = Verb ;            
    V2 = Verb ** {comp : Str ; cas : Case } ;
    AdA = {s : Str} ;
    Pol = {s : Str ; b : Bool} ;
    Tense = {s : Str ; t : TTense} ;
    Conj = {s : Str ; n : Number} ;
  lin
    UseCl t p cl = {s = t.s ++ p.s ++ cl.s ! ClDir ! t.t ! p.b} ; 
    PredVP np vp = {
      s = \\d,t,b => 
        let 
          vps = vp.verb.s ! d ! t ! b ! np.a 
        in case d of {
         ClDir => np.s ! Nom ++ vps.fin  ++ vps.inf ++ vp.compl ! np.a ;
         ClInv => vps.fin ++ "go" ++ np.s ! Nom ++ vps.inf ++ vp.compl ! np.a 
          }
      } ;

    ComplV2 v2 np = {
     verb = agrV v2 ; 
     compl = \\_ => np.s ! v2.cas ++ v2.comp
      } ;

    UseV v = {
       verb = agrV v ;
       compl = \\_ => []
       };

    DetCN det cn = {
     s = \\c => det.s ! c ++ cn.s ! det.n  ! c ;
     a = Ag det.n Per3
    } ;

    ModCN ap cn = {
      s = \\n,c => ap.s ! AAttr ! n  ++ cn.s ! n ! c
      } ;

    CompAP ap = {
      verb = agrV copula ;
      compl = table {Ag num _ => ap.s ! APred ! num}
      } ;


    AdAP ada ap = {
      s = \\n,c => ada.s ++ ap.s ! n ! c
     } ;

    ConjS  co x y = {s = x.s ++ co.s ++ y.s} ;
    ConjAP co x y = {s = \\af,n => x.s ! af ! n ++ co.s ++ y.s ! af ! n} ;

    ConjNP co nx ny = {
      s = \\c => nx.s ! c ++ co.s ++ ny.s ! c ;
      a = conjAgr co.n nx.a ny.a
      } ;

    UseN n = n ;

    UseA adj = adj ;

    a_Det = mkDet "" Sg ;

    every_Det = mkDetCase "buohkat" Pl ;

    the_Det = mkDet "" Sg ;
        
        
-- this as "the one you point at", not as "the one you think about"    
    this_Det = mkDetCase "dát" Sg ;
    these_Det = mkDetCase "id" "dát" Pl ; -- med lok
    that_Det = mkDetCase "duot" Sg ;
    those_Det = mkDetCase "duot" Pl ;

    i_NP   =   pronNP "mon" "munnje"   Sg Per1 ;
    she_NP = pronNP "son" "sutnje"   Sg Per3 ;
    youSg_NP = pronNP "don" "dutnje" Sg Per2 ;
    he_NP = pronNP "son" "sutnje"   Sg Per3 ; 
    -- you, they and we can either be two persons (Du) or more (Pl)
    youPl_NP = pronNP "ddi" "didjiide" Pl Per2 | pronNP "doai" "dudnuide" Du Per2;
    they_NP = pronNP "sii" "sidjiide" Pl Per3  | pronNP "soai" "sudnuide" Du Per3 ;
    we_NP =  pronNP "mii" "midjiide" Pl Per1   | pronNP "moai" "munnuide" Du Per1 ;

    very_AdA = ss "hui" ;

    Pos  = {s = [] ; b = True } ;
    Neg  = {s = [] ; b = False } ;
    Pres = {s = [] ; t = TPres } ;
    Perf = {s = [] ; t = TPerf } ;
    Past = {s = [] ; t = TPast } ;
    Fut  = {s = [] ; t = TFut } ;

    and_Conj = {s = "ja"     ; n = Pl} ;
    or_Conj  = {s = "dahege" ; n = Sg} ;

-- more

  lincat
    Utt = {s : Str} ; 
    QS  = {s : QForm => Str} ; 
    QCl = {s : QForm => TTense => Bool => Str} ; 
    ClSlash = {s : ClForm => TTense => Bool => Str ; comp : Str ; c : Case} ;  
    Adv  = {s : Str ; isPre : Bool } ;
    Prep = { c : Case ; comp : Str ; isPre : Bool } ;
    VS = Verb ;
    VQ = Verb ** {comp : Agr => Str}; 
    VV = {s : AgrVerb } ; 
    IP = {s : Number => Case => Str} ;
    PN = {s : Number => Case => Str} ;
    IAdv, Subj = {s : Str} ;

  lin
    UttS s = s ;
    UttQS s = {s = s.s ! QDir} ;

    UseQCl t p cl = {s = \\q => t.s ++ p.s ++ cl.s ! q ! t.t ! p.b} ; 

    QuestCl cl = {s = \\q,t,p => 
      case q of {
        QDir   => cl.s ! ClInv ! t ! p ;
        QIndir => "juosgo" ++ cl.s ! ClDir ! t ! p
        }
      } ;

    QuestVP ip vp = {
     s = \\q,t,p => 
        let 
          vps = vp.verb.s ! ClDir ! t ! p ! Ag Sg Per3 
        in
          ip.s ! Sg ! Nom  ++ vps.fin ++ vps.inf ++ vp.compl ! Ag Sg Per3 
      } ;


    QuestSlash ip cls = {
        s = (\\q,t,p => ip.s ! Sg ! cls.c ++ cls.comp ++ cls.s ! ClDir ! t ! p ) 
    } ;

    QuestIAdv iadv cl = {s = \\q,t,p => 
      iadv.s ++ 
      case q of {
        QDir   => cl.s ! ClDir ! t ! p ;
        QIndir => cl.s ! ClDir ! t ! p 
        }
      } ;

    SubjCl cl subj s = {
      s = \\d,t,b => cl.s ! d ! t ! b ++ subj.s ++ s.s
      } ;

    CompAdv adv = {
      verb = agrV copula ; 
      compl = \\ag => adv.s
      } ;

    PrepNP prep np = {
      s = np.s ! prep.c ++ prep.comp ;
      isPre = prep.isPre
      } ;

    ComplVS v s = {
      verb = agrV v ;
      compl = \\_ => "ahte" ++ s.s
      } ;

    ComplVQ v q = {
      verb = agrV v ;
      compl = \\a => v.comp ! a ++ q.s ! QIndir
      } ;


    ComplVV v vp = {
      verb = v.s ;
      compl =  \\a => infVP a vp ;
        
      } ;

    SlashV2 np v2 = {
      s = \\d,t,b => 
        let 
          vps = (agrV v2).s ! d ! t ! b ! np.a 
        in case d of {
          ClDir => np.s ! Nom ++ vps.fin ++ vps.inf ;
          ClInv => vps.fin ++ np.s ! Nom ++ vps.inf
          } ;
      comp = v2.comp ;
      c = v2.cas
      } ;


    SlashPrep cl prep = {
      s    = \\d,t,b => cl.s ! d ! t ! b ;
      comp = prep.comp ;
      c    = prep.c 
      } ;

    AdvVP vp adv = {
      verb = vp.verb ;
      compl = \\a => vp.compl ! a ++ adv.s
      } ;

    UsePN pn = { s = pn.s ! Sg ; a = Ag Sg Per3}  ;

    AdvNP np adv = {
      s = \\c => preOrPost adv.isPre  (adv.s) (np.s ! c) ;
      a = np.a
      } ;



    who_IP  = { s = makeIP "gii" "gean" } ;
    here_Adv = { s = "dás" | "dáppe" ; isPre = False } ;
    by_Prep   = { c = Acc ; comp = "luhtte" ; isPre = False } ;
    in_Prep   = { c = Lok ; comp = [] ; isPre = False} ;
    of_Prep   = { c = Acc ; comp = [] ; isPre = True } ;
    with_Prep = { c = Kom ; comp = [] ; isPre = False} ;

    can_VV  = {s = mkVV "sáhttit"  "sáhht" } ; 
    must_VV = {s = mkVV "fertet"  "fert" } ; 
    want_VV = {s = mkVV "dáhttut"  "dáht" } ; 

    although_Subj = ss "vaikko" ;
    because_Subj = ss "danin go" ;
    when_Subj = ss "go" ; 

    when_IAdv = ss "goas" ;
    where_IAdv = ss "gos" ;
    why_IAdv = ss "manne" ;
}
