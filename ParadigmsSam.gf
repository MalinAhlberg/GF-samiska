resource ParadigmsSam = GrammarSam [N,A,V] ** 
  open ResSam, GrammarSam, Prelude in {


param 
  -- Saami inflects verbs and nouns in these three categories, this cannot really
  -- be implemented through a smart paradigm and must be given in lexicon.
  -- verbs under ROdd can only end in "it"
  -- Contract are "joined words" that form a noun or a verb 
  InflectPar = Even | Odd | Contract ;

oper

  mkN = overload {
    mkN : (nissu : Str) -> N  -- nissu is the noun in nominativ
      = \n -> lin N (regNoun n (evenOrOdd n)) ;
    mkN : (muorra, muora : Str) -> N  -- muorroa : Nominativ, muora : Accusative/Genetive
      = \s,p -> lin N (mkNoun s p (evenOrOdd p)) ;
    mkN : (nissu : Str) -> InflectPar -> N  -- nissu is the noun in nominativ
      = \n,i -> lin N (regNoun n (inflect2RInflect i)) ;
    mkN : (muorra, muora : Str) -> InflectPar -> N  -- muorroa : Nominativ, muora : Accusative/Genetive
      = \s,p,i -> lin N (mkNoun s p (inflect2RInflect i)) 
    } ;

  mkPN = overload{
   mkPN : (john : Str) -> PN
     = \s -> lin PN (regNoun s (inflect2RInflect Even)) ; 
   mkPN : (merja,merjja : Str) -> PN
     = \s,p -> lin PN (mkNoun s p (inflect2RInflect Even) )
   } ; 

  mkA = overload {
    mkA : (ruoksat,rukses : Str) -> A   -- (nominative, attribute)
      = \a,b -> lin  A (mkAdj1 a b) ;
    mkA : (x,y,z : Str) -> A
      = \a,b,c -> lin A (mkAdj2 a b c) ;  --(nominative sg, nominative pl, attribute)
    mkA : (ruona : Str) -> A
      = \a -> lin A (regAdj a) ;
    } ;

  mkV = overload {
    mkV : (verb : Str) -> V
       = \v -> lin V (regVerb v (evenOrOdd v)) ;
    mkV : (vazzit,vacc : Str) -> V
       = \vanlig,stam -> lin V (mkVerb vanlig stam (evenOrOdd vanlig)) ;
    mkV : (verb : Str) -> InflectPar -> V
      = \v,i -> lin V (regVerb v (inflect2RInflect i)) ;
    mkV : (vazzit,vacc: Str) -> InflectPar -> V 
      = \vanlig,stam,i -> lin V (mkVerb vanlig stam (inflect2RInflect i)) ;
    } ;

  mkV2 = overload {
    mkV2 : V -> V2
      = \v -> lin V2 (v ** {comp = [] ; cas = Acc }) ;
    mkV2 : V -> Str -> V2
      = \v,p -> lin V2 (v ** {comp = p; cas = Acc}) ;
    mkV2 : V -> Str -> Case -> V2
      = \v,co,ca -> lin V2 (v ** {comp = co; cas = ca})
    } ;
    
  mkVQRefl : V -> VQ = \v -> lin VQ (v ** {comp = refl}) ;

  inflect2RInflect : InflectPar -> RInflectPar =
   \pi -> case pi of {
     Even     => REven ;
     Odd      => ROdd ;
     Contract => RContract 
     };
     

}
