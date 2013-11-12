(* -------------------------------------------------------------------- *)
record 'a myrecord = { x : 'a; y : 'a; }.

op r (x y : 'a) = {| x = x; y = y; |}.

lemma L (x y : 'a) : (r x y).(| x |) = x.
proof. by rewrite /r. qed.

lemma LE (v : 'a myrecord): v = {| x = v.(| x |); y = v.(| y |); |}.
proof. by elim/myrecord_ind v. qed.