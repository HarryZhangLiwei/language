#lang racket
(require racket/async-channel)
(require (except-in eopl #%module-begin))
(provide (all-from-out eopl))
(require test-engine/scheme-gui)

;;;;;;;;;;;;;;;;;;;    scanner     ;;;;;;;;;;;;;;;;;;;;;;;
(define syntax '((whitespace (whitespace) skip)
                 (comment ("%" (arbno (not #\newline))) skip)
                 (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)
                 (number (digit (arbno digit)) number)))

(define scanner-spec-1 (sllgen:make-string-scanner syntax '()))

;;;;;;;;;;;;;;;;;;;       parse      ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define grammar '((program ("begin" (arbno func_def) "end") a-program)
                  
                  (func_def ("main function" "{" (arbno statement) "}") main_func_stmt)

                  (func_def ("function" identifier list_arg "{" (arbno statement) "}") no_return_func_stmt)

                  (list_arg ("()") empty_arg)

                  (list_arg ("(" (arbno  identifier) ")") nonempty_arg)

                  (statement ("var"  identifier "=" expression ";") decl_stmt)       ;;;if just one exp -> error  need init

                  (statement (expression "=" expression ";") eq_stmt)

                  (statement ("print" expression ";") print_stmt)

                  (statement ("if"  (arbno "::" expression "->" (arbno statement)) "fi") if_mul_stmt)

                  (statement ("do" (arbno "::"  expression  "->" (arbno statement)) "od") repet_mul_stmt)

                  (statement ("for" "("  statement expression ";"   statement ")" "{" (arbno statement) "}") for_stmt)

                  (statement ("active asy-proctype" identifier "()" "{" (arbno statement) "}") process_asy_stmt)

                  (statement ("active syn-proctype" identifier "()" "{" (arbno statement) "}") process_syn_stmt)

                  (statement ("run" expression list_arg ";") run_stmt)

                  (statement ("kill" "(" expression ")" ";") kill_stmt)

                  (statement ("break;") break_stmt)

                  (statement ("sleep" "(" number ")" ";") sleep_stmt)

                  (statement ("if(" expression ")" "{" (arbno statement) "}" "else" "{" (arbno statement )"}") if_stmt)

                  (statement ("channel-syn" "{" "thread: "(arbno expression)";" "resources:" (arbno expression) ";" "}") channel_syn_stmt)

                  (statement ("channel-asy" "{" "thread: "(arbno expression)";" "resources:" (arbno expression) ";" "}") channel_asy_stmt)

                  (statement ("start"  list_arg  ";") start_stmt)

                  (statement ("wait" "(" expression ")" ";") wait_stmt)
                  
                  (var_val (expression "=" expression) var_val_rule)

                  (expression ("(" expression operator expression ")") op_exp)

                  (expression (logical "(" expression expression ")") log_exp)

                  (expression ("&&" "(" expression expression ")") and_exp)

                  (expression ("||" "(" expression expression ")") or_exp)

                  (expression ("[" (arbno expression) "]") array_exp)

                  (expression (number) lit_exp)

                  (expression (identifier) var_exp)
                
                  (logical (">") greater_lo)

                  (logical ("<") less_lo)

                  (logical ("==") eq_lo)

                  (logical (">=") greater_eq_lo)

                  (logical ("<=") less_eq_lo)

                  (operator ("+") plus_op)

                  (operator ("-") minu_op)

                  (operator ("*") muti_op)

                  (operator ("/") divi_op)))

;;;;;;;;;;;;;;;;;;;; init datatype  ;;;;;;;;;;;;;;
(sllgen:make-define-datatypes syntax grammar)

;;;;;;;;;;;;;;;;;;;;  other related-parser ;;;;;;;;;;;;;;;;;;
;; show : () -> datatype
(define show (lambda() (sllgen:list-define-datatypes syntax grammar)))

;; justscan string -> token
(define justscan (sllgen:make-string-scanner syntax grammar))

;; scan&parse : string -> syntax
(define scan&parse (sllgen:make-string-parser syntax grammar))
;;;;;;;;;;;;;;;;;;  Hval ;;;;;;;;;;;;;;;;;;;;

(define-datatype hval hval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?))
  (ref-val (ref reference?))
  (process-val (proce process?)))

;;;;;;;;;;;;;;;; initial environment ;;;;;;;;;;;;;;;;

  (define init-env 
    (lambda ()
      (empty-env)))
;;;;;;;;;;;;;;;;;;  store  ;;;;;;;;;;;;;;;;;;;;

(define empty-store
  (lambda () '()))

(define the-store 'uninitialized)

(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))


;;;;;;;;;;;;;;;;;;  ref-op  ;;;;;;;;;;;;;;;;;;;

(define reference?
  (lambda (v)   (integer? v)))

(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store (append the-store (list val))) next-ref)))

(define deref
  (lambda (ref)
    (list-ref the-store ref)))

(define setref!
  (lambda (ref val)
    (set! the-store
          (letrec ((setref-inner
                    (lambda (store1 ref1) (cond ((null? store1)
                                                 (report-invalid-reference ref the-store))
                                                ((zero? ref1)
                                                 (cons val (cdr store1)))
                                                (else
                                                 (cons (car store1) (setref-inner (cdr store1) (- ref1 1))))))))
            (setref-inner the-store ref)))))

(define report-invalid-reference
  (lambda (ref store) 'wrong))

(define run
    (lambda (string)
    (value-of-program (scan&parse string))))

;;; extractors:

  (define hval->normal
    (lambda (v)
      (cases hval v
        (num-val (num) num)
        (ref-val (ref) (hval->normal (deref ref)))
        (else (hval-extractor-error 'normal v)))))
  ;; hval->num : HVal -> Int
  (define hval->num
    (lambda (v)
      (cases hval v
	(num-val (num) num)
	(else (hval-extractor-error 'num v)))))

  ;; hval->bool : HVal -> Bool
  (define hval->bool
    (lambda (v)
      (cases hval v
	(bool-val (bool) bool)
	(else (hval-extractor-error 'bool v)))))

  ;; expval->proc : HVal -> Proc
  (define hval->proc
    (lambda (v)
      (cases hval v
	(proc-val (proc) proc)
	(else (hval-extractor-error 'proc v)))))

;; hval->ref : HVal -> Ref
  (define hval->ref
    (lambda (v)
      (cases hval v
	(ref-val (ref) ref)
	(else (hval-extractor-error 'proc v)))))

;; hval->process: HVal -> Process
  (define hval->process
    (lambda (v)
      (cases hval v
        (process-val (pro) pro)
        (else (hval-extractor-error 'proc v)))))

  (define hval-extractor-error
    (lambda (variant value)
      (eopl:error 'hval-extractors "Looking for a ~s, found ~s"
	variant value)))

  (define run-extractor-error
    (lambda ()
      (eopl:error 'if-statement "Looking for right condition!")))

  (define run-do-extractor-error
    (lambda ()
      (eopl:error 'Do-statement "Looking for right condition!")))

  (define main-extractor-error
    (lambda ()
      (eopl:error 'program-run-error "Looking for main function!")))

 (define check-op
   (lambda (op v)
     (if (equal? / op) (if (equal? 0 v) (zero-error) op) op)))

(define zero-error
  (lambda ()
    (eopl:error 'program-value-error "Looking for non 0 value")))


;;;;;;;;;;;;;;;;;;  env   ;;;;;;;;;;;;;;;;;;;;;


(define empty-env-record
    (lambda () 
      '()))

(define extended-env-record
  (lambda (sym val old-env)
    (cons (list sym val) old-env)))
  
(define empty-env-record? null?)

(define environment?
  (lambda (x)
    (or (empty-env-record? x)
        (and (pair? x)
             (symbol? (car (car x)))
             (hval? (cadr (car x)))
             (environment? (cdr x))))))

(define empty-env
  (lambda ()
    (empty-env-record)))

  
  (define empty-env? 
    (lambda (x)
      (empty-env-record? x)))

  (define extend-env
    (lambda (sym val old-env)
      (extended-env-record sym val old-env)))

  (define apply-env
    (lambda (env search-sym)
      (if (empty-env? env)
	(eopl:error 'apply-env "No binding for ~s" search-sym)
	(let ((sym (extended-env-record->sym env))
	      (val (extended-env-record->val env))
	      (old-env (extended-env-record->old-env env)))
	  (if (eqv? search-sym sym)
	    val
	    (apply-env old-env search-sym))))))

;;;;;;;;;;;;;;;;;;; env helper   ;;;;;;;;;;;;

(define extended-env-record->sym
  (lambda (r)
    (car (car r))))

(define extended-env-record->val
  (lambda (r)
    (cadr (car r))))

(define extended-env-record->old-env
  (lambda (r)
    (cdr r)))

;;;;;;;;;;;;;;;; closure ;;;;;;;;;;;;;;;;

  ;; proc? : SchemeVal -> Bool
  ;; procedure : Var * Exp * Env -> Proc
(define-datatype proc proc?
    (procedure
      (var list-symbol?)
      (body list-statement?)
      (env environment?)))

(define list-symbol?
    (lambda (var)
      (if (null? var) #t (if (symbol? (car var)) (and #t (list-symbol? (cdr var))) #f))))

(define list-statement?
    (lambda (var)
      (if (null? var) #t (if (statement? (car var)) (and #t (list-statement? (cdr var))) #f))))

;;;;;;;;;;;;;;;;;;; process datatype ;;;;;;;;;;;

 ;; procedure : Var * Exp * Env -> Proc

(define syn-processer
   (lambda (name body env)
     (thread
      (lambda ()
       (begin (value-of-statement body env)
       (let loop ()
       (define item (channel-get work-channel))
       (case item
         [(DONE)
          (channel-put result-channel
                       (format "Thread ~a done" name))]
         [else
          (channel-put result-channel
                       (format "Thread ~a processed ~a" name
                               item))
          (loop)])))))))

(define asy-processer
  (lambda (name body env)
  (thread
   (lambda ()
     (begin (value-of-statement body env)
     (let loop ()
       (define item (async-channel-get work-channel-asy))
       (safer-printf "Thread ~a processing item: ~a" name item)
       (loop)))))))

(define process?
  (lambda (pro)
    (if (thread? pro) #t #f)))

;;;;;;;;;;;;;;;;;;; interpter;;;;;;;;;;;;;;;;


(define value-of-program
  (lambda (fun)
    (cases program fun
      (a-program (stmt) (value-of-fun stmt (init-env) (initialize-store!))))))

(define value-of-fun
  (lambda (stmte env store)
    (if (null? stmte) (main-extractor-error) 
    (cases func_def (car stmte)  
      (main_func_stmt (stmt)  (value-of-statement stmt env))
      
      (no_return_func_stmt (name arg stmt)
                           (let ((val (proc-val (procedure (value-of-arg arg) stmt env))))
                             (value-of-fun (cdr stmte) (extend-env name (ref-val (newref val)) env) store)))))))

(define value-of-statement
  (lambda (stmte env)
    (if (null? stmte) "stmt-success"
    (cases statement (car stmte) 
      (eq_stmt  (var exp)
                  (let ((v2 (value-of-expression exp env)))
                    (begin (setref! (hval->ref(value-of-expression  var env)) v2) (value-of-statement (cdr stmte) env))))

      (if_stmt (exp stmt1 stmt2) (if (value-of-expression exp env)
                                     (begin (value-of-statement stmt1 env) (value-of-statement (cdr stmte) env))
                                     (begin (value-of-statement stmt2 env) (value-of-statement (cdr stmte) env))))

      (for_stmt (stmt exp stmt1 stmt2) (let ((var (value-of-statement (list stmt) env)))
                                         (letrec ((for
                                                      (lambda (exp stmt1 stmt2 stmte env)
                                                            (if (value-of-expression exp env)
                                                                (let ((var1 (value-of-statement  stmt2 env))
                                                                      (var2 (value-of-statement  (list stmt1) env)))
                                                                  (for exp stmt1 stmt2 stmte env))
                                                                (value-of-statement (cdr stmte) env)))))
                                           (for exp stmt1 stmt2 stmte env))))


      (if_mul_stmt (exp stmt)
                   (let ((condition (map (lambda (x) (value-of-expression x env)) exp)))
                     (excute-random condition stmt stmte env)))

      (break_stmt () 'stop)
      
      (repet_mul_stmt (exp stmt)
                      (let ((condition (map (lambda (x) (value-of-expression x env)) exp)))
                        (do-excute-random condition stmt stmte env)))

      (process_syn_stmt (exp stmt) (let ((val  (process-val (syn-processer exp stmt env))))
                                 (value-of-statement (cdr stmte) (extend-env exp val env))))

      (process_asy_stmt (exp stmt) (let ((val  (process-val (asy-processer exp stmt env))))
                                 (value-of-statement (cdr stmte) (extend-env exp val env))))

         
      (channel_asy_stmt (thread res) (let ((var (map (lambda (x) (hval->process (value-of-expression x env))) thread)))
                                            (begin (for ([item res]) (async-channel-put work-channel-asy item)) (value-of-statement (cdr stmte) env))))

      (channel_syn_stmt (thread res) (let ((var (map (lambda (x) (hval->process (value-of-expression x env))) thread)))
                                            (begin (for ([item (map (lambda (x)(value-of-expression x env)) res)])
                                              (channel-put work-channel item)) (value-of-statement (cdr stmte) env))))

      (start_stmt (stmt) 
                (begin (map (lambda (x) (hval->process (value-of-expression (var_exp x) env))) (value-of-arg stmt)))
                (value-of-statement (cdr stmte) env))

      (kill_stmt (exp)
                 (kill-thread (hval->process (value-of-expression exp env))))

      (wait_stmt (exp)
                 (thread-wait (hval->process (value-of-expression exp env))))

      (sleep_stmt (num)
                  (sleep (value-of-expression num env)))

      (run_stmt (name rand)
                (let ((proc (hval->proc (deref (hval->ref (value-of-expression name env)))))
                      (arg (value-of-arg rand)))
                  (begin (apply-procedure proc arg) (value-of-statement (cdr stmte) env))))
      
      (print_stmt (exp)
                  (let ((v1 (value-of-expression exp env)))
                    (let ((ref1 (hval->ref v1)))
                      (display (deref ref1))(newline)
                      (value-of-statement (cdr stmte) env))))
      
      (decl_stmt (var exp)
                 (let ((v1 (value-of-expression exp env)))
                   (value-of-statement (cdr stmte) (extend-env var (ref-val (newref v1)) env))))))))

(define value-of-arg
  (lambda (arg)
    (cases list_arg arg
      (empty_arg () '())
      (nonempty_arg (var) var))))


(define value-of-expression
  (lambda (exp env)
    (cases expression exp
      (lit_exp (num) (num-val num))
      
      (op_exp (v1 op v2) (num-val ((check-op (value-of-operator op) (hval->normal (value-of-expression v2 env)))
                                   (hval->normal (value-of-expression v1 env)) (hval->normal (value-of-expression v2 env)))))   ;;;;;check  /0
      
      (var_exp (var)  (apply-env env var))

      (log_exp (log exp exp1) ((value-of-logical log) (hval->normal (value-of-expression exp env)) (hval->normal (value-of-expression exp1 env))))

      (and_exp (exp exp1) (and (value-of-expression exp env) (value-of-expression exp1 env)))

      (or_exp (exp exp1) (or (value-of-expression exp env) (value-of-expression exp1 env)))

      (array_exp (arr) (map (lambda (x) (value-of-expression x env)) arr)))))

(define value-of-operator
  (lambda (op)
    (cases operator op
      (plus_op () +)
      (minu_op () -)
      (muti_op () *)
      (divi_op () /))))

(define value-of-logical
  (lambda (lg)
    (cases logical lg
      (greater_lo () >)
      (less_lo () <)
      (greater_eq_lo () >=)
      (less_eq_lo () <=)
      (eq_lo () equal?))))

 ;; apply-procedure : Proc * HVal -> Expression
  (define apply-procedure
    (lambda (proc1 val)
      (cases proc proc1
        (procedure (var body saved-env)
          (value-of-statement body (extend-env var val saved-env))))))

;;;;;;;;;;;;;; random ;;;;;;;;;;;;;;;;;
;; excute-random : List * State-List * State-List * Env -> Expression

(define excute-random
  (lambda (con stmt stmte env)
    (if (equal? 0 (count-true con)) (run-extractor-error)
        (let ((temp (excute-one (random (count-true con)) stmt con env)))
          (value-of-statement (cdr stmte) env)))))

(define count-true
  (lambda (con)
    (if (null? con) 0 (if (equal? #t (car con))
                          (+ 1 (count-true (cdr con))) (count-true (cdr con))))))

(define excute-one
  (lambda (num stmt con env)
    (if (equal? 0 num) (value-of-statement (car stmt) env)
        (if (equal? #t (car con))
            (excute-one (- num 1) (cdr stmt) (cdr con) env) (excute-one num (cdr stmt) (cdr con) env)))))  


(define value-of-var_val
  (lambda (var_rul env)
    (cases var_val var_rul
      (var_val_rule (exp1 exp2) (let ((var (value-of-expression exp1 env))
                                      (val (value-of-expression exp2 env)))
                                  (extend-env var val env))))))

(define do-excute-random
  (lambda (con stmt stmte env)
    (if (equal? 0 (count-true con)) (run-do-extractor-error)
        (do-excute-one (random (count-true con)) stmt con env stmte stmt con))))

(define do-excute-one
  (lambda (num stmt con env stmte stmt1 con1)
    (if (equal? 0 num)
        (if (equal? (list (break_stmt)) (car stmt))
            (let ((var (value-of-statement (car stmt) env))) (value-of-statement (cdr stmte) env))
            (let ((var (value-of-statement (car stmt) env))) (do-excute-random con1 stmt1 stmte env)))
        (if (equal? #t (car con))
            (do-excute-one (- num 1) (cdr stmt) (cdr con) env stmte stmt1 con1) (do-excute-one num (cdr stmt) (cdr con) env stmte stmt1 con1)))))



;;;;;;;;;;;;;;;;;;;;;;;;   channel   ;;;;;;;;;;;;;;;;;;;;;;;

(define result-channel (make-channel))

(define result-thread
        (thread (lambda ()
                  (let loop ()
                    (displayln (channel-get result-channel))
                    (loop)))))

(define work-channel (make-channel))


(define print-thread
  (thread (lambda ()
            (let loop ()
              (displayln (thread-receive))
              (loop)))))

(define (safer-printf . items)
  (thread-send print-thread
               (apply format items)))
 
(define work-channel-asy (make-async-channel 1))


;;;;;;;;;;;;;;;;;;;;;;;;;   test   ;;;;;;;;;;;;;;;;;;;;;;;;;

;(run "begin function a(){ var i=10; if(> (i 3)){var m=0; m=10; print m;} else {var m=0; m=22; print m;} } main function {run a();}end")
;
;(run "begin function a(){var sum =0; var i=0; for(i=0; <(i 10); i=(i + 1);){  sum = (sum + i); print sum;} } main function {run a();} end")
;
;
;(run "begin function a(){ if::&&(>(4 5) ==(3 3)) ->  var m=0; m=10; print m; ::&&(>(4 5) ==(3 3)) ->  var m=0; m=4; print m;fi var y=9;} main function{ run a();} end")
;
;(run "begin  function b(){var sum =0; sum = (sum / 0); var i=0; for(i=0; <(i 10); i=(i + 1);){  sum = (sum + i); print sum;} }
;function a(){ if::&&(>(6 5) ==(3 3)) ->  var m=0; m=10; print m; ::&&(>(7 5) ==(3 3)) ->  var m=0; m=4; print m;fi var y=9;} main function{ run a(); run b(); } end")
;
;(run "begin function a(){ do::&&(>(6 5) ==(3 3)) ->  var m=0; m=10; print m; ::&&(>(7 5) ==(3 3)) ->
;ar m=0; m=4; print m; ::&&(>(7 5) ==(3 3)) ->  var m=0; m=11; print m; ::&&(>(7 5) ==(3 3)) ->  break; od var y=9;} main function{ run a();} end")
;
;
;(run "begin function a(){var i = (0 +(9*2)) ;var u=[1 2 3]; var w=0; var q=(1+2); print i;} main function{ run a(); }  end")
;
;(run  "begin main function {
;active asy-proctype a(){
;   var m = 0;
;   print m;
;}
;active syn-proctype b(){
;   wait(a);
;   var m = 1;
;   print m;
;}
;start(a b);
;} end")
;
;(run "begin main function {
;
;active asy-proctype a(){
;   var m = 0;
; 
;}
;
;active asy-proctype b(){
;   var m = 1;  
;}
;
;active asy-proctype c(){
;   var m = 1;
; print m;
;}
;
;channel-asy{
;  thread: a b c;
;  resources: 1 2 3 4 5 6;
;}
;} end")
;;
;(run "begin main function {
;active syn-proctype a(){
;   var m = 0;
;  
;}
;
;active syn-proctype b(){
;   var m = 1;
;   
;}
;
;active syn-proctype c(){
;   var m = 1;
;   
;}
;
;channel-syn{
;  thread: a b c;
;  resources: 1 2 3 4 5 6;
;}
;
;} end")



