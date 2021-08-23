#lang racket
(require redex)
(require "../dada.rkt")

(redex-let*
 Dada
 [(ty_my_string (term (my String ())))
  (expr_new_string (term (class-instance String () ())))
  (ty_my_Character (term (my Character ())))
  (ty_sh_String (term ((shared ((shared (char name)))) String ())))
  (ty_my_Pair (term (my Pair (ty_sh_String int))))
  ]
 
 (dada-check-pass
  ; We are able to track the dependency on `tmp.a`
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, shared(tmp.a.name) String> = Pair(give char, give pair.a);
  ; }
  (seq ((var (char ty_my_Character) = (class-instance Character () (22 expr_new_string 44)))
        (var (pair ty_my_Pair) = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var (tmp
              (my Pair (ty_my_Character
                        ((shared ((shared (tmp a name)))) String ()))))
             = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a name)))) String ())) ((give (char)) (give (pair a)))))
        )))
    
 (dada-check-pass
  ; We are able to upcast from "tmp.a.name" to "tmp.a"
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, shared(tmp.a) String> = Pair(give char, give pair.a);
  ; }
  (seq ((var (char ty_my_Character) = (class-instance Character () (22 expr_new_string 44)))
        (var (pair ty_my_Pair) = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var (tmp
              (my Pair (ty_my_Character
                        ((shared ((shared (tmp a)))) String ()))))
             = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a)))) String ())) ((give (char)) (give (pair a)))))
        )))

 (dada-check-pass
  ; We can upcast from shared(tmp.a) to shared(tmp)
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, shared(tmp) String> = Pair(give char, give pair.a);
  ; }
  (seq ((var (char ty_my_Character) = (class-instance Character () (22 expr_new_string 44)))
        (var (pair ty_my_Pair) = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var (tmp
              (my Pair (ty_my_Character
                        ((shared ((shared (tmp)))) String ()))))
             = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a)))) String ())) ((give (char)) (give (pair a)))))
        )))

 (dada-check-pass
  ; We are able to track the dependency on `tmp.a` through to tmp2.a
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, shared(tmp.a.name) String> = Pair(give char, give pair.a);
  ;   var tmp2: my Pair<my Character, shared(tmp2.a.name) String> = give tmp;
  ; }
  (seq ((var (char ty_my_Character) = (class-instance Character () (22 expr_new_string 44)))
        (var (pair ty_my_Pair) = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var (tmp
              (my Pair (ty_my_Character
                        ((shared ((shared (tmp a name)))) String ()))))
             = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a name)))) String ())) ((give (char)) (give (pair a)))))
        (var (tmp2
              (my Pair (ty_my_Character
                        ((shared ((shared (tmp2 a name)))) String ()))))
             = (give (tmp)))
        )))

 (dada-check-fail
  ; We cannot upcast from shared(tmp.a) to shared(char.name)
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, shared(char.name) String> = Pair(give char, give pair.a);
  ; }
  (seq ((var (char ty_my_Character) = (class-instance Character () (22 expr_new_string 44)))
        (var (pair ty_my_Pair) = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var (tmp
              (my Pair (ty_my_Character
                        ((shared ((shared (char name)))) String ()))))
             = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a)))) String ())) ((give (char)) (give (pair a)))))
        )))

 (dada-check-fail
  ; We cannot upast from shared(tmp.a.name) to shared()
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, our String> = Pair(give char, give pair.a);
  ; }
  (seq ((var (char ty_my_Character) = (class-instance Character () (22 expr_new_string 44)))
        (var (pair ty_my_Pair) = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var (tmp
              (my Pair (ty_my_Character
                        (our String ()))))
             = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a)))) String ())) ((give (char)) (give (pair a)))))
        )))
 )


(dada-check-pass
 ; {
 ;   var v: Vec<String> = Vec("foo");
 ;   var s: shared(v) String = share v[0];
 ;   var m: Message<String> = Message(v, s);
 ; }
 (seq ((var (v (my Vec ((my String ())))) = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       #;(var (v2 (my Vec ((my String ())))) = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var (s ((shared ((shared (v)))) String ())) = (share (v value0)))
       (var (m (my Message ((my String ())))) = (class-instance Message ((my String ())) ((give (v)) (give (s)))))
       ))
 )

(dada-check-fail
 ; {
 ;   var v: Vec<String> = Vec("foo");
 ;   var v2: Vec<String> = Vec("bar");
 ;   var s: shared(v) String = share v[0];
 ;   var m: Message<String> = Message(v2, s); // ERROR
 ; }
 (seq ((var (v (my Vec ((my String ())))) = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var (v2 (my Vec ((my String ())))) = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var (s ((shared ((shared (v)))) String ())) = (share (v value0)))
       (var (m (my Message ((my String ())))) = (class-instance Message ((my String ())) ((give (v2)) (give (s)))))
       ))
 )