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
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (var pair = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var tmp = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a name)))) String ())) ((give (char)) (give (pair a)))))
        (assert-ty (tmp) : (my Pair (ty_my_Character
                                     ((shared ((shared (tmp a name)))) String ()))))
        )))
    
 (dada-check-pass
  ; We are able to upcast from "tmp.a.name" to "tmp.a"
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, shared(tmp.a) String> = Pair(give char, give pair.a);
  ; }
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (var pair = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var tmp = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a)))) String ())) ((give (char)) (give (pair a)))))
        (assert-ty (tmp) : (my Pair (ty_my_Character
                                     ((shared ((shared (tmp a)))) String ()))))
        )))

 (dada-check-pass
  ; We can upcast from shared(tmp.a) to shared(tmp)
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, shared(tmp) String> = Pair(give char, give pair.a);
  ; }
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (var pair = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var tmp = ((class-instance Pair (ty_my_Character ((shared ((shared (in-flight a)))) String ())) ((give (char)) (give (pair a))))
                    : (my Pair (ty_my_Character
                                ((shared ((shared (in-flight)))) String ())))))
        (assert-ty (tmp) : (my Pair (ty_my_Character
                                     ((shared ((shared (tmp)))) String ()))))
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
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (var pair = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var tmp = (class-instance Pair (ty_my_Character ((shared ((shared (in-flight a name)))) String ())) ((give (char)) (give (pair a)))))
        (assert-ty (tmp) : (my Pair (ty_my_Character
                                     ((shared ((shared (tmp a name)))) String ()))))
        (var tmp2 = (give (tmp)))
        (assert-ty (pair) : (my Pair (((shared ((shared (tmp2 a name)))) String ()) int)))
        (assert-ty (tmp2) : (my Pair (ty_my_Character
                                      ((shared ((shared (tmp2 a name)))) String ()))))
        )))

 (dada-check-fail
  ; We cannot upcast from shared(tmp.a) to shared(char.name)
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, shared(char.name) String> = Pair(give char, give pair.a);
  ; }
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (var pair = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var tmp = ((class-instance Pair (ty_my_Character ((shared ((shared (in-flight a)))) String ())) ((give (char)) (give (pair a))))
                    : (my Pair (ty_my_Character
                                ((shared ((shared (char name)))) String ())))))
        )))

 (dada-check-fail
  ; We cannot upast from shared(tmp.a.name) to shared()
  ;
  ; {
  ;   var char: my Character = Character(22, "Achilles", 44)
  ;   var pair: my Pair<shared(char.name) String, int> = Pair(share char.name, 66);
  ;   var tmp: my Pair<my Character, our String> = Pair(give char, give pair.a);
  ; }
  program_test
  (seq ((var char = (class-instance Character () (22 expr_new_string 44)))
        (var pair = (class-instance Pair (ty_sh_String int) ((share (char name)) 66)))
        (var tmp = ((class-instance Pair (ty_my_Character ((shared ((shared (in-flight a)))) String ())) ((give (char)) (give (pair a))))
                    : (my Pair (ty_my_Character
                                (our String ())))))
        )))
 )

(dada-check-pass
 ; {
 ;   var v: Vec<String> = Vec("foo");
 ;   var s: shared(v) String = share v[0];
 ;   var m: Message<String> = Message(v, s);
 ; }
 program_test
 (seq ((var v = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       #;(var v2 = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var s = (share (v value0)))
       (var m = (class-instance Message ((my String ())) ((give (v)) (give (s)))))
       (assert-ty (m) : (my Message ((my String ()))))
       (assert-ty (s) : ((shared ((shared (m vec value0)))) String ()))
       ))
 )

(dada-check-fail
 ; {
 ;   var v: Vec<String> = Vec("foo");
 ;   var v2: Vec<String> = Vec("bar");
 ;   var s: shared(v) String = share v[0];
 ;   var m: Message<String> = Message(v2, s); // ERROR
 ; }
 program_test
 (seq ((var v = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var v2 = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var s = (share (v value0)))
       (var m = (class-instance Message ((my String ())) ((give (v2)) (give (s)))))
       ))
 )

(dada-check-fail
 ; We should *not* be able to track the dependency on `v`
 ; when we have something borrowed.
 ;
 ; {
 ;   var v: my Vec<String> = Vec("foo");
 ;   var p: borrowed(v) Vec<String> = lend v;
 ;   var v2 = v;
 ;   p[0] = "bar";
 ; }
 program_test
 (seq ((var v = (class-instance Vec ((my String ())) ((class-instance String () ()))))
       (var p = (lend (v)))
       (var v2 = (give (v)))
       (set (p value0) = (class-instance String () ()))
       ))
 )

