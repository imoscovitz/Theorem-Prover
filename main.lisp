;;;;
;;;; A(x) (cond (equal x 'Ilan Moscovitz) (x = (author this)))
;;;; A propositional logic resolution theorem prover
;;;;

(defun prove (clauses)
(format t "~& CLAUSES TO PROVE: ~s" clauses)
  (let ((proved nil))
    (do ((clauses1 (cdr clauses) (cdr clauses1)))
          ((or (not (null proved)) (null clauses1)) proved)
          (format t "~& .")
          (format t "~&~&~&------~s-----" clauses1)
          (do ((clauses2 clauses (cdr clauses2)))
              ((or (not (null proved)) (equal clauses1 clauses2)) proved)
                (let ((resolution (resolve (car clauses2) (car clauses1))))
                  (format t "~& ~s     ~s" (car clauses2) (car clauses1))
                  (cond ((equal '(nil) resolution)
                          (setf proved t))
                        ((not (equal 'FAIL resolution))
                        (format t "~& RESOLUTION: ~s" resolution)
                          (setf clauses (append clauses resolution))
                          (setf clauses1 (append clauses1 resolution))
                          (setf clauses2 (append clauses2 resolution)))))))))

(defun rewrite-formulas (formulas)
  (let ((formulas-CNF))
    (dolist (formula-CNF formulas formulas-CNF)
      (setf formulas-CNF (append formulas-CNF (rewrite-formula formula-CNF)))
      (format t "~&~s    |    ~s" (rewrite-formula formula-CNF) formulas-CNF))))

(defun rewrite-formula (formula)
  (resyntax-clause
          (distribute-djs
                (literalize-negs
                  (rewrite-conds formula)))))

(defun resolve (clause1 clause2)
  (let ((resolution 'FAIL))
    (do ((remain1 clause1 (cdr remain1)))
        ((or (not (equal 'FAIL resolution)) (null remain1)) resolution)
        (do ((remain2 clause2 (cdr remain2)))
            ((or (not (equal 'FAIL resolution)) (null remain2)) resolution)
            (if (contradict (car remain1) (car remain2))
                      (setf resolution
                        (list (append
                          (remove (car remain1) clause1)
                          (remove (car remain2) clause2)))))))))

(defun contradict (element1 element2)
  (cond ((and (atom element1) (not (atom element2)))
          (equal element1 (second element2)))
        ((and (not (atom element1)) (atom element2))
          (equal (second element1) element2))
        (t nil)))

(defun resyntax-clause (clause)
  (cond ((= 1 (length clause)) (list clause))
        ((= 2 (length clause)) (list (list clause)))
        ((equal 'and (first clause)) (resyntax-and clause))
        (t (list (resyntax-or clause)))))

(defun resyntax-and (node)
  (cond ((atom node) (list (list node)))
        ((= 2 (length node)) (list node))
        ((equal 'and (first node)) (append (resyntax-and (second node)) (resyntax-and (third node))))
        (t (list (resyntax-or node)))))

(defun resyntax-or (node)
  (cond ((atom node) (list node))
        ((= 2 (length node)) (list node))
        (t (append (resyntax-or (second node)) (resyntax-or (third node))))))

(defun remove-cjs (formula)
  (cond
    ((atom formula) formula)
    ((= 1 (length formula)) formula)
    (t (let ((bindings (match formula '(and (? x) (? y)))))
         (cond ((not (null bindings))
                (let ((phi (remove-cjs (second (first bindings))))
                      (psi (remove-cjs (second (second bindings)))))
                  (list phi psi)))
               ((eq 'not (car formula))
                (list (car formula) (remove-cjs (second formula))))
               (t (list (car formula)
                        (remove-cjs (second formula))
                        (remove-cjs (third formula)))))))))

(defun remove-djs (formula)
  (cond
    ((atom formula) formula)
    ((= 1 (length formula)) formula)
    (t (let ((bindings (match formula '(or (? x) (? y)))))
         (cond ((not (null bindings))
                (let ((phi (remove-djs (second (first bindings))))
                      (psi (remove-djs (second (second bindings)))))
                  (list phi psi)))
               ((eq 'not (car formula))
                (list (car formula) (remove-djs (second formula))))
               (t (list (car formula)
                        (remove-djs (second formula))
                        (remove-djs (third formula)))))))))

(defun rewrite-conds (formula)
  (cond
    ((atom formula) formula)
    ((= 1 (length formula)) formula)
    (t (let ((bindings (match formula '(cond (? x) (? y)))))
         (cond ((not (null bindings))
                (let ((phi (rewrite-conds (second (first bindings))))
                      (psi (rewrite-conds (second (second bindings)))))
                  (list 'or (list 'not phi) psi)))
               ((eq 'not (car formula))
                (list (car formula) (rewrite-conds (second formula))))
               (t (list (car formula)
                        (rewrite-conds (second formula))
                        (rewrite-conds (third formula)))))))))

(defun literalize-negs (formula)
  (do* ((current-formula formula
                         literate-formula)
        (literate-formula (demorgan-djs (demorgan-cjs (remove-dns formula)))
                          (demorgan-djs (demorgan-cjs (remove-dns literate-formula)))))
       ((equal current-formula literate-formula) literate-formula)))

(defun remove-dns (formula)
  (cond
    ((atom formula) formula)
    ((= 1 (length formula)) formula)
    (t (let ((bindings (match formula '(not (not (? x))))))
         (cond ((not (null bindings))
                (let ((phi (remove-dns (second (first bindings)))))
                    phi))
               ((eq 'not (car formula))
                (list (car formula) (remove-dns (second formula))))
               (t (list (car formula)
                        (remove-dns (second formula))
                        (remove-dns (third formula)))))))))

(defun demorgan-djs (formula)
 (cond
   ((atom formula) formula)
   ((= 1 (length formula)) formula)
   (t (let ((bindings (match formula '(not (or (? x) (? y))))))
        (cond ((not (null bindings))
               (let ((phi (demorgan-djs (second (first bindings))))
                     (psi (demorgan-djs (second (second bindings)))))
                 (list 'and (list 'not phi) (list 'not psi))))
              ((eq 'not (car formula))
               (list (car formula) (demorgan-djs (second formula))))
              (t (list (car formula)
                       (demorgan-djs (second formula))
                       (demorgan-djs (third formula)))))))))

(defun demorgan-cjs (formula)
  (cond
    ((atom formula) formula)
    ((= 1 (length formula)) formula)
    (t (let ((bindings (match formula '(not (and (? x) (? y))))))
         (cond ((not (null bindings))
                (let ((phi (demorgan-cjs (second (first bindings))))
                      (psi (demorgan-cjs (second (second bindings)))))
                  (list 'or (list 'not phi) (list 'not psi))))
               ((eq 'not (car formula))
                (list (car formula) (demorgan-cjs (second formula))))
               (t (list (car formula)
                        (demorgan-cjs (second formula))
                        (demorgan-cjs (third formula)))))))))

(defun distribute-djs (formula)
  (do* ((current-formula formula
                         literate-formula)
        (literate-formula (distribute-djs-left (distribute-djs-right formula))
                          (distribute-djs-left (distribute-djs-right literate-formula))))
       ((equal current-formula literate-formula) literate-formula)))

(defun distribute-djs-right (formula)
  (cond
    ((atom formula) formula)
    ((= 1 (length formula)) formula)
    (t (let ((bindings (match formula '(or (and (? x?) (? y)) (? z)))))
         (cond ((not (null bindings))
                (let ((psi (distribute-djs-left (second (first bindings))))
                      (chi (distribute-djs-left (second (second bindings))))
                      (phi (distribute-djs-left (second (third bindings)))))
                  (list 'and (list 'or phi psi) (list 'or phi chi))))
               ((eq 'not (car formula))
                (list (car formula) (distribute-djs-right (second formula))))
               (t (list (car formula)
                        (distribute-djs-right (second formula))
                        (distribute-djs-right (third formula)))))))))

(defun distribute-djs-left (formula)
  (cond
    ((atom formula) formula)
    ((= 1 (length formula)) formula)
    (t (let ((bindings (match formula '(or (? x) (and (? y?) (? z))))))
         (cond ((not (null bindings))
                (let ((phi (distribute-djs-left (second (first bindings))))
                      (psi (distribute-djs-left (second (second bindings))))
                      (chi (distribute-djs-left (second (third bindings)))))
                  (list 'and (list 'or phi psi) (list 'or phi chi))))
               ((eq 'not (car formula))
                (list (car formula) (distribute-djs-left (second formula))))
               (t (list (car formula)
                        (distribute-djs-left (second formula))
                        (distribute-djs-left (third formula)))))))))

(defun example1 ()
  (let* ((wffs '((cond p q)
                 (cond q r)
                 ((not r))
                 (p)))       ; negated conclusion
         (clauses (rewrite-formulas wffs)))
    (format t "Original formulas: ~a~%" wffs)
    (format t "Formulas in CNF: ~a~%" clauses)
    (prove clauses)))

(defun example2 ()
  (let* ((wffs '((cond (not hf) w)
                 (cond (not w) (not brd))
                 (cond (not (and brd (not w))) hf)
                 (cond (not (or (not hf) (not brd))) (not brch))
                 (brd)
                 (brch)))    ; negated conclusion
         (clauses (rewrite-formulas wffs)))
    (format t "Original formulas: ~a~%" wffs)
    (format t "Formulas in CNF: ~a~%" clauses)
    (prove clauses)))

(defun example3 ()
  (let* ((wffs '((cond p (not r))
                  (cond (or q p) (or r q))
                  (not q)
                  (p)))
                     ; negated conclusion
         (clauses (rewrite-formulas wffs)))
    (format t "Original formulas: ~a~%" wffs)
    (format t "Formulas in CNF: ~a~%" clauses)
    (prove clauses)))

(defun example4 ()
  (let* ((wffs '((cond p q)
                (cond (not p) r)
                (cond (not q) (not r))
                ((not p))))

                     ; negated conclusion
         (clauses (rewrite-formulas wffs)))
    (format t "Original formulas: ~a~%" wffs)
    (format t "Formulas in CNF: ~a~%" clauses)
    (prove clauses)))


(defun example5 ()
  (let* ((wffs '((cond (cond s p) r)
                ((not r))
                (cond (cond (p q) (cond x r)))
                (x)))

         (clauses (rewrite-formulas wffs)))
    (format t "Original formulas: ~a~%" wffs)
    (format t "Formulas in CNF: ~a~%" clauses)
    (prove clauses)))




;; The following match and related functions courtesy Brown University
;; Copyright 1994, Brown University, Providence, RI
;; See end of file for full copyright information

;; (in-package 'user)

;; Matching from the logic chapter.

(defun is-VAR (x) (and (consp x) (eq (first x) '?)))

;; Determine if a constant and a pattern match.
(defun match (const pat)
  (aux-match const pat '((match t))))

;; Keep track of the bindings established so far.
(defun aux-match (const pat bdgs)
  (cond ((not bdgs) nil)
        ((atom pat) (if (eq pat const) bdgs nil))
        ;; If the pattern is a bound variable, match the
        ;; constant and whatever the variable is bound to.
        ;; If the pattern is a variable and not bound,
        ;; then bind the variable to the constant.
        ((is-VAR pat)
         (let ((bdg (assoc pat bdgs :test #'equal)))
           (cond (bdg (aux-match const (second bdg) bdgs))
                 (t (cons (list pat const) bdgs)))))
        ((or (atom const) (null const)) nil)
        (t (aux-match (first const)
                      (first pat)
                      (aux-match (rest const)
                                 (rest pat) bdgs)))))

;; Test MATCH
(defun test ()
  (and (match '(loves (dog fred) fred) '(loves (? x) (? y)))
       (match '(loves (dog fred) mary) '(loves (dog (? x)) (? y)))
       (not (match '(loves (dog fred) fred) '(loves (? x) (? x))))
       (not (match '(loves (dog fred) mary) '(loves (dog (? x)) (? x))))))


;; Copyright 1994, Brown University, Providence, RI
;; Permission to use and modify this software and its documentation
;; for any purpose other than its incorporation into a commercial
;; product is hereby granted without fee.  Permission to copy and
;; distribute this software and its documentation only for
;; non-commercial use is also granted without fee, provided, however
;; that the above copyright notice appear in all copies, that both
;; that copyright notice and this permission notice appear in
;; supporting documentation, that the name of Brown University not
;; be used in advertising or publicity pertaining to distribution
;; of the software without specific, written prior permission, and
;; that the person doing the distribution notify Brown University
;; of such distributions outside of his or her organization. Brown
;; University makes no representations about the suitability of this
;; software for any purpose. It is provided "as is" without express
;; or implied warranty.  Brown University requests notification of
;; any modifications to this software or its documentation.
;;
;; Send the following redistribution information
;;
;;   Name:
;;   Organization:
;;   Address (postal and/or electronic):
;;
;; To:
;;   Software Librarian
;;   Computer Science Department, Box 1910
;;   Brown University
;;   Providence, RI 02912
;;
;;     or
;;
;;   brusd@cs.brown.edu
;;
;; We will acknowledge all electronic notifications.
