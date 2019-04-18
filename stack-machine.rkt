#lang racket
(require "opcodes.rkt")
(provide make-stack-machine)
(provide run-stack-machine)
(provide get-stack)
(provide get-varnames)
(provide get-consts)
(provide get-names)
(provide get-code)
(provide get-IC)
(provide empty-stack)
(provide make-stack)
(provide push)
(provide pop)
(provide top)


(define empty-stack '())
(define (make-stack) (list))

(define (push element stack) (cons element stack))
(define (top stack) (car stack))
(define (pop stack) (if (null? stack)
                        stack
                        (cdr stack)))

;; Initializes a new stack-machine.
;; '(empty-stack (hash) (hash) (hash) '(( . ) ( . ) ( . )) 0)
(define (make-stack-machine stack co-varnames co-consts co-names co-code IC)
  (list stack co-varnames co-consts co-names co-code IC))

;; Returns a hashmap of (variable, value)
;; ex: 
;; > (get-varnames (make-stack-machine empty-stack 'dummy-co-varnames (hash) (hash) (list) 0))
;; 'dummy-co-varnames
(define (get-varnames stack-machine) (second stack-machine))

;; Returns constants (initialization / operation values)
;; ex:
;; > (get-consts (make-stack-machine empty-stack (hash) 'dummy-co-consts (hash) (list) 0))
;; 'dummy-co-consts
(define (get-consts stack-machine) (third stack-machine))

;; Returns the names of the functions that will be called
;; ex:
;; > (get-names (make-stack-machine empty-stack (hash) (hash) 'dummy-co-names (list) 0))
;; 'dummy-co-names
(define (get-names stack-machine) (fourth stack-machine))

;; Returns the operation codes
;; ex:
;; > (get-code (make-stack-machine empty-stack (hash) (hash) (hash) 'dummy-co-code 0))
;; dummy-co-code
(define (get-code stack-machine) (fifth stack-machine))

;; Returns the execution stack
;; ex:
;; > (get-stack (make-stack-machine 'dummy-exec-stack (hash) (hash) (hash) (list) 0))
;; dummy-exec-stack
(define (get-stack stack-machine) (car stack-machine))

;; Returns the INSTRUCTION-COUNTER
;; ex:
;; > (get-IC (make-stack-machine empty-stack (hash) (hash) (hash) (list) 0))
;; 0
(define (get-IC stack-machine) (sixth stack-machine))



(define symbols (list 'STACK 'CO-VARNAMES 'CO-CONSTS 'CO-NAMES 'CO-CODE 'INSTRUCTION-COUNTER))

; Returns the index of the symbol
;; As long as the stack-machine is defined in the same order as the symbols, searching
;; through the 'symbols' list and returning the index will do the trick
(define (get-symbol-index symbol)
  (let get_idx ((idx 0) (L symbols))
    (if (null? L)
        #f
        (if (equal? symbol (car L))
            idx
            (get_idx (add1 idx) (cdr L))))))

; Returns a new, updated stack-machine
;; > (get-varnames (update-stack-machine "new-varnames" 'CO-VARNAMES stack-machine))
;; "new-varnames"
;; > (get-varnames (update-stack-machine "new-names" 'CO-NAMES stack-machine))
;; "new-names"
(define (update-stack-machine item symbol stack-machine)
  (list-set stack-machine (get-symbol-index symbol) item))

; Pushes [value] into the execution stack of the stack-machine
(define (push-exec-stack value stack-machine)
  (update-stack-machine (push value (get-stack stack-machine)) 'STACK stack-machine))

; Pops the execution stack of the stack-machine
(define (pop-exec-stack stack-machine)
  (update-stack-machine (pop (get-stack stack-machine)) 'STACK stack-machine))

; Returns the top of the execution stack
(define (get-tos stack-machine)
  (top (get-stack stack-machine)))

; Returns the item underneath the top of the execution stack
(define (get-tos1 stack-machine)
  (get-tos (pop-exec-stack stack-machine)))

; Pushes the name of the next function into the stack
(define (LOAD_GLOBAL arg stack-machine)
  (push-exec-stack (hash-ref (get-names stack-machine) arg) stack-machine))

; Pushes CO-CONSTS[arg] on top of the stack
(define (LOAD_CONST arg stack-machine)
  (push-exec-stack (hash-ref (get-consts stack-machine) arg) stack-machine))

; Assigns value of TOS to CO-VARNAMES[arg]
(define (STORE_FAST arg stack-machine)
  (pop-exec-stack (update-stack-machine (hash-set (get-varnames stack-machine) arg (top (get-stack stack-machine))) 'CO-VARNAMES stack-machine)))

; Pushes the element found in CO-VARNAMES[arg] onto stack
(define (LOAD_FAST arg stack-machine)
  (push-exec-stack (hash-ref (get-varnames stack-machine) arg) stack-machine))

; Executes 'func' between TOS and TOS1. Used for BINARY_OPERATIONS and
; COMPARE_OPERATIONS
(define (BINARY_OPERATION func stack-machine)
  (push-exec-stack (func (get-tos1 stack-machine) (get-tos stack-machine)) (pop-exec-stack (pop-exec-stack stack-machine))))

; Jumps to a specific operation by updating the INSTRUCTION COUNTER
(define (JUMP_ABSOLUTE arg stack-machine)
  (update-stack-machine (/ arg 2) 'INSTRUCTION-COUNTER stack-machine))

; Decides if it will enter the 'if' block by comparing the
; boolean value on the top of the stack pushed by COMPARE_OP
; which evaluates the condition
(define (POP_JUMP_IF_FALSE arg stack-machine)
  (if (false? (get-tos stack-machine))
      (pop-exec-stack (JUMP_ABSOLUTE arg stack-machine))
      (pop-exec-stack stack-machine)))

; Executes next(TOS). If a value is returned, it's pushed on the top of the stack
; and updates the iterators. If null is returned, the loop is finished and jumps
; to the specified instruction
(define (FOR_ITER arg stack-machine)
  (if (null? (get-tos stack-machine))
      (pop-exec-stack (JUMP_ABSOLUTE (+ (* (get-IC stack-machine) 2) arg 2) stack-machine))
      (push-exec-stack (car (get-tos stack-machine)) (push-exec-stack (cdr (get-tos stack-machine)) (pop-exec-stack stack-machine)))))

; Calls the according function pushed onto stack
(define (CALL_FUNCTION arg stack-machine)
  (let ((args (take (get-stack stack-machine) arg)) (func_key (list-ref (get-stack stack-machine) arg)))
    (push-exec-stack ((hash-ref functions func_key) args) (update-stack-machine (drop (get-stack stack-machine) (add1 arg)) 'STACK stack-machine))))    

; Parses the process code and calls the according proc
(define (decide_proc code arg stack-machine)
  (case code
    [(LOAD_CONST) (LOAD_CONST arg stack-machine)]
    [(LOAD_FAST) (LOAD_FAST arg stack-machine)]
    [(STORE_FAST) (STORE_FAST arg stack-machine)]
    [(BINARY_ADD) (BINARY_OPERATION + stack-machine)]
    [(BINARY_SUBTRACT) (BINARY_OPERATION - stack-machine)]
    [(BINARY_MODULO) (BINARY_OPERATION modulo stack-machine)]
    [(INPLACE_ADD) (BINARY_OPERATION + stack-machine)]
    [(INPLACE_SUBTRACT) (BINARY_OPERATION - stack-machine)]
    [(INPLACE_MODULO) (BINARY_OPERATION modulo stack-machine)]
    [(COMPARE_OP) (BINARY_OPERATION (list-ref cmpcodes arg) stack-machine)]
    [(POP_JUMP_IF_FALSE) (POP_JUMP_IF_FALSE arg stack-machine)]
    [(JUMP_ABSOLUTE) (JUMP_ABSOLUTE arg stack-machine)]
    [(FOR_ITER) (FOR_ITER arg stack-machine)]
    [(CALL_FUNCTION) (CALL_FUNCTION arg stack-machine)]
    [(LOAD_GLOBAL) (LOAD_GLOBAL arg stack-machine)]
    [(POP_TOP) (pop-exec-stack stack-machine)]
    [else stack-machine]))

;; UTILS:
(define (get_op_pair stack-machine)
  (list-ref (get-code stack-machine) (get-IC stack-machine)))

(define (get_current_op_code stack-machine)
  (car (get_op_pair stack-machine)))

(define (get_current_op_arg stack-machine)
  (cdr (get_op_pair stack-machine)))

; Runs all the operation codes
(define (run-stack-machine stack-machine)
  (let run_procs ((st stack-machine))
    (if (equal? (get_current_op_code st) 'RETURN_VALUE)
        st
        (run_procs (decide_proc (get_current_op_code st) (get_current_op_arg st) (update-stack-machine (add1 (get-IC st)) 'INSTRUCTION-COUNTER st))))))
