--# -path=.:prelude:alltenses

concrete LexiconSam of Lexicon = GrammarSam ** open ParadigmsSam, Prelude in {

flags 
  optimize=values ; coding=utf8 ;


lin
 man_N =  mkN "olmmái" "olbmá" Contract ;
 woman_N = mkN "nisson" "nissona"  ;
 house_N = mkN "viessu" "viesu"  ;
 tree_N = mkN "muorra" "muora"  ; 
 
 
 big_A = mkA "stuoris" "stuorrát" "stoura" ; 
 small_A = mkA "unni" "unna" ; 
 green_A = mkA "ruoná" ; 
 

 walk_V = mkV "vázzit" "vácc" ; 
 arrive_V = mkV "boahtit" "boađ" ; 
 sleep_V = mkV "oađđit" "oađ" ;   
 
 love_V2 = mkV2 (mkV "ráhkistit" ) ; 
 please_V2 = mkV2 (mkV "duđahit" ) ; 
 look_V2 = mkV2 (mkV "geahččat" "geahč" ) "guvlui";
 
 believe_VS = mkV "jáhkkit" "jáhk" ;  
 know_VS = mkV "diehtit" "dieđ" ;  
 wonder_VQ = mkVQRefl (mkV "jearrat" "jear" ) ; -- "i ask if..." reflexive verb
 
 john_PN = mkPN "Jovna" "Jovnna"  ;
 mary_PN = mkPN "Márjá" "Márjjá" ;

} ;
