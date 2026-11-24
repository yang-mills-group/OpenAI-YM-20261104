import YM.RG12.Strike.Fare
/-!
# Exact continuum resonance test: TWO legs attaching from a single cubic integrated vertex

Normalized conventions for each contraction arm (hold color on both contracted legs and
third exterior leg fixed, multiply by arbitrary color tensors or structure constants after):
 -- uses Feynman line 1/x², normalized (common (4π²)^-1 doesn't affect cancellation),
    curl slots at the tested external mark, derivative lists `L,K` at that mark, summed
    against arbitrary antisymmetric tensors U V (note these needn't carry any extra symmetry
    or obey field equations). Common displacement sign choices don't affect these
    results by homogeneity/linearity. Include the actual curl 2 by checking curl lemma.
 -- normalization polynomial not in these terms. Tested only at resonance (jet derivative count
    k=L.length+K.length+3). k1,k3 results in other files. Inputs are jets of harmonic
    divergence-free outer potential on the separated domain (API `Clean`); see
    our bridges for sourcing this from cylinders at free order without assuming WilsonX.
 -- Annulus weight: ANY custom `Dried`, in particular differences and dilation
    derivatives of smooth radial Taylor cutoffs =1 near zero. No MSbar or fermionic
    conventions imported.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical

abbrev Foil := Axis4 → Axis4 → ℂ
def anti (T:Foil):Prop:=∀ i j:Axis4,T i j = -T j i
abbrev tube (p:Cells)(x:R):ℂ:= barrage field p x
-- arm with mark derivatives L and connection index j (potential leg polarization).
-- computes ∑i U_{ij2} contracted with ∂_{i,L}G δ_{j2,j}-∂_{j2,L}G δ_{i,j} via `curl_at`
def leg (T:Foil)(L:Cells)(i:Axis4)(D:Cells)(x:R):ℂ:=∑ j:Axis4,2*T j i * tube (D++L++[j]) x
lemma curls (T:Foil)(hT:anti T)(L D:Cells)(s:Axis4)(x:R):leg T L s D x=
   ∑ i:Axis4,∑ j:Axis4,T i j*( (if j=s then tube (D++L++[i]) x else 0)-(if i=s then tube (D++L++[j]) x else 0)):=by
   simp_rw [mul_sub,Finset.sum_sub_distrib,mul_ite,mul_zero]; rw [sum_comm (f:=fun i:Axis4=>fun j:Axis4=>if i=s then _ else (0:ℂ))]
   simp_rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ (_:Axis4)),← Finset.sum_sub_distrib]; unfold leg; apply sum_congr rfl; intro j _; conv_rhs=> rhs; rw [hT]
   ring
abbrev Poll:= Axis4→Cells→ℂ
structure Clean (P:Poll)(n:ℕ):Prop where
    form (i:Axis4) : Rated n (P i)
    focused {u:Cells} (h:u.length+1=n): ∑ i:Axis4,P i (i::u)=0

-- concrete resonance operations, use V3 (∂_i A_j) A_i A_j.
variable {w:R→ℂ}(P:Poll)(L K:Cells)(U V : Foil)(hU:anti U)(hV:anti V)
def score (L K:Cells):ℕ:=L.length+K.length+3
set_option quotPrecheck false
local notation "m!"=>score L K
abbrev sep (n:ℕ)(p:Cells→ℂ)(x:R):= fall (gauge n p) x
-- variant: can interpret derivative leg on slotA or slotB by swapping those input slots.
def rowA (w:R→ℂ):ℂ := ∑ i:Axis4,∑ j:Axis4,
   ∫ x:R, w x * sep m! (P j) x*(leg U L j [i] x*leg V K i [] x)
def rowB (w:R→ℂ) :ℂ := ∑ i:Axis4,∑ j:Axis4,
   ∫ x:R,w x*sep m! (P i) x*(leg U L j [i] x*leg V K j [] x)
def rowC (w:R→ℂ):ℂ:=∑ i:Axis4,∑ j:Axis4,
   ∫ x:R,w x * sep (m!-1) (fun l=>P j (i::l)) x*(leg U L i [] x*leg V K j [] x)
-- orientation factor structure: if uncontracted is exterior j, connected other derivatives
-- mark labels visit i and j, order relevant for color only. If ∂ uncontracted on j,
-- Taylor data are P_j(i::L').

section financial
variable (hw: Dried w)
include hw
lemma pairing (n)(A B:Cells)(P:Cells→ℂ): Integrable (fun x=>w x * sep n P x *(tube A x*tube B x)):=by
   obtain ⟨S,hS,he⟩:=fire A;obtain ⟨T,ht,hF⟩:=fire B
   have hf0:w 0=0:=hw.near.eq_of_nhds
   suffices he': (fun x=> w x * sep n P x *(tube A x*tube B x))=(fun x=> w x * sep n P x * (scripts (pin A::S) x*scripts (pin B::T) x)) by rw [he']; exact pour_table hw ..
   funext x; by_cases h:x=0
   · subst x;simp [hf0]
   exact congr_arg₂ (fun v s=> _ * (v*s)) (he x h) (hF x h)
-- generalized factor movement
lemma shed (n:ℕ)(P:Cells→ℂ) (i j:Axis4)(p s:Cells) :
    (∫ x:R, w x * sep n P x* (leg U L i p x * leg V K j s x)) = 4* ∑ a:Axis4,∑ b:Axis4, U a i*V b j *
       (∫ x:R,w x *sep n P x*(tube (p++L++[a]) x* tube (s++K++[b]) x)) :=by
   let u (a b:Axis4)(x:R):= w x * sep n P x * (tube (p++L++[a]) x* tube (s++K++[b]) x)
   have hu (a b):Integrable (fun x=> (4*(U a i*V b j))*u a b x) := (pairing hw n _ _ P).const_mul _
   have he(x): w x * sep n P x * (leg U L i p x * leg V K j s x) = ∑ a:Axis4,∑ b:Axis4,(4*(U a i*V b j))*u a b x:=by
       unfold leg; simp_rw [Finset.sum_mul,Finset.mul_sum]; apply sum_congr rfl; intro a _; apply sum_congr rfl;intro b _; unfold u; ring
   simp only [he]; rw [integral_finsetSum (f:=fun a (x:R)=> ∑ b:Axis4,(4*(U a i*V b j))*u a b x)]
   · rw [mul_sum]; apply sum_congr rfl; intro a _; rw [integral_finsetSum _ (fun b _=>hu a b),mul_sum]; apply sum_congr rfl;intro b _; unfold u; rw [MeasureTheory.integral_const_mul]; ring
   intro a _; apply integrable_finsetSum;exact fun b _=> hu _ b
end financial
-- algebra beyond extremal collapse
private lemma twist (T:Foil)(hT:anti T)(f:Axis4→Axis4→ℂ)(hf:∀ i j,f i j=f j i): ∑ i:Axis4,∑ j:Axis4,T i j*f i j=0:=by
   let s:= ∑ i:Axis4,∑ j:Axis4,T i j*f i j
   have he : s= -s:=by
      unfold s; simp_rw [← Finset.sum_neg_distrib]; rw [sum_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; nth_rw 1 [hf]; rw [hT i j]; ring
   change s=0; linear_combination 1/2*he
private lemma spin {P:Poll}{n:ℕ}(hP:Clean P n)(i j k:Axis4)(v:Cells)(u:Cells)(hv:v.length+u.length+2=n) : P i (j::(v++[k])++u)=P i (k::(v++[j])++u):=by
   -- parse: cons binds one side? use list_perm
   apply (hP.form i).sym
   · have he (j k:Axis4): List.Perm (j::(v++[k])++u) (j::k::(v++u)):=by
        -- `List.Perm.middle`, append etc
        simp only [List.cons_append,List.append_assoc]
        exact List.Perm.cons j (List.perm_middle (l₁:=v) (l₂:=u) (a:=k)) -- name
     refine (he j k).trans (_root_.List.Perm.trans (List.Perm.swap k j (v++u)) (he k j).symm)
   simp only [List.length_cons,List.length_append,List.length_nil]; omega
-- special case when k at end after two appends
private lemma whirl {P:Poll}{n:ℕ}(hP: Clean P n)(u:Cells)(j k:Axis4)(l:Cells)(v:Axis4)(hu:u.length+l.length+2=n): P v ((j::u)++l++[k])=P v ((k::u)++l++[j]):=by
   have he:= spin hP v j k (u++l) [] (by simpa using hu); simpa only [List.cons_append,List.append_nil,List.append_assoc,List.singleton_append] using he
set_option linter.unusedSectionVars false
variable (h: Dried w)(hP:Clean P (score L K))
include h hP hV
-- lengths of resonant jets retained by conversion, helps avoiding dependent casts
local notation:max "pp:" i "," a:max=> [i]++L++[(a:Axis4)]
local notation:max "sss!" b:max=> ([]:Cells)++K++[(b:Axis4)]
lemma sinkA :rowA P L K U V w=0:=by
   let n:=1+L.length+1; let m:=0+K.length+1
   have hh: n+m= m! :=by unfold n m score; omega
   obtain ⟨c,hc⟩:= workbench h n m
   let Q(j a i b:Axis4):= P j ((i::L++[a])++(K++[b]))
   let z:=4*c
   have he(i j:Axis4) : (∫ x:R, w x * sep m! (P j) x*(leg U L j [i] x*leg V K i [] x)) = ∑ a:Axis4,∑ b:Axis4,z * (U a j*V b i) * Q j a i b:=by
      rw [← hh,shed L K U V h (n+m) (P j) j i [i] [],Finset.mul_sum]; apply sum_congr rfl; intro a _; rw [Finset.mul_sum]; apply sum_congr rfl;intro b _
      change 4*(U a j * V b i * ∫ x:R,w x* fall (gauge (n+m) (P j)) x*(barrage field _ x * barrage field _ x))=_
      rw [hc (P j) (hh.symm ▸ hP.form j) (pp: i,a) (sss! b) (by simp [n,add_comm]) (by simp [m])]
      unfold z Q; simp only [List.nil_append,List.cons_append];ring -- list simplifies
   unfold rowA; simp_rw [he]; rw [sum_comm]; apply sum_eq_zero;intro j _
   rw [sum_comm];apply sum_eq_zero; intro a _
   have hq: (∑ i:Axis4,∑ b:Axis4,z*(U a j*V b i)*Q j a i b)= z*U a j *∑ i:Axis4,∑ b:Axis4,V b i* Q j a i b:=by simp only [mul_sum,mul_assoc]
   rw [hq,sum_comm, twist V hV (fun b i=> Q j a i b),mul_zero]
   intro i b; unfold Q
   have hx:= whirl hP (L++[a]) b i K j (by unfold score;simp;omega); simpa [List.cons_append,List.append_assoc] using hx

omit hV in
lemma sinkB :rowB P L K U V w=0:=by
   let n:=1+L.length+1; let m:=0+K.length+1
   have hh: n+m= m! :=by unfold n m score; omega
   obtain ⟨c,hc⟩:= workbench h n m
   let Q(j a i b:Axis4):= P i ((i::L++[a])++(K++[b]))
   let z:=4*c
   have he(i j:Axis4) : (∫ x:R, w x * sep m! (P i) x*(leg U L j [i] x*leg V K j [] x)) = ∑ a:Axis4,∑ b:Axis4,z * (U a j*V b j) * Q j a i b:=by
      rw [← hh,shed L K U V h (n+m) (P i) j j [i] [],Finset.mul_sum]; apply sum_congr rfl; intro a _; rw [Finset.mul_sum]; apply sum_congr rfl;intro b _
      change 4*(U a j * V b j * ∫ x:R,w x* fall (gauge (n+m) (P i)) x*(barrage field _ x * barrage field _ x))=_
      rw [hc (P i) (hh.symm ▸ hP.form i) (pp: i,a) (sss! b) (by simp [n,add_comm]) (by simp [m])]
      unfold z Q; simp only [List.nil_append,List.cons_append];ring -- list simplifies
   unfold rowB; simp_rw [he]; rw [sum_comm]; apply sum_eq_zero;intro j _
   rw [sum_comm]; apply sum_eq_zero; intro a _; rw [sum_comm];apply sum_eq_zero; intro b _
   rw [← Finset.mul_sum]
   have hQ : (∑ i:Axis4,P i (i::(L++[a]++(K++[b]))))=0:=hP.focused (by unfold score;simp; omega)
   have hr:(∑ i:Axis4,Q j a i b)=0:=by simpa [Q,List.cons_append,List.append_assoc] using hQ
   rw [hr,mul_zero]
-- derivative on uncontracted leg
omit hV
include hU
lemma sinkC :rowC P L K U V w=0:=by
   let n:=L.length+1; let m:=K.length+1
   have hh:n+m= m!-1:=by unfold n m score;omega
   let F(i j:Axis4)(u:Cells):=P j (i::u)
   have he(i j:Axis4) : Rated (n+m) (F i j):= ⟨fun hs ht=>(hP.form j).sym (List.Perm.cons i hs) (by simp only [List.length_cons,ht]; unfold n m score;omega),fun {u} hz=>by
      have he:u.length+1+2=m!:=by unfold n m at *; unfold score;omega
      have hs(a:Axis4):List.Perm (i::a::a::u) (a::a::i::u):= by exact (List.Perm.swap a i (a::u)).trans (List.Perm.cons a (List.Perm.swap a i u))
      have hu(a): P j (i::a::a::u) = P j (a::a::i::u) := (hP.form j).sym (hs a) (by simp only [List.length_cons]; omega)
      unfold F; simp_rw [hu];exact (hP.form j).clean (by rwa [List.length_cons])⟩
   obtain ⟨c,hc⟩:= workbench h n m
   let Q(j b i a:Axis4):=F i j ((L++[a])++(K++[b]))
   let z:=4*c
   have hr(i j:Axis4) :(∫ x:R,w x * sep (m!-1) (F i j) x*(leg U L i [] x*leg V K j [] x))=∑ a:Axis4,∑ b:Axis4,z * (V b j *U a i)* Q j b i a:=by
      rw [← hh, shed L K U V h (n+m) (F i j) i j [] [],Finset.mul_sum]; apply sum_congr rfl; intro a _; rw [Finset.mul_sum]; apply sum_congr rfl;intro b _
      change 4*(U a i * V b j * ∫ x:R,w x* fall (gauge (n+m) (F i j)) x*(barrage field _ x * barrage field _ x))=_
      rw [hc (F i j) (he i j) (([]:Cells)++L++[a]) (([]:Cells)++K++[b]) (by simp [n]) (by simp [m])]; unfold Q F z ; simp only [List.nil_append];ring
   unfold rowC
   change ∑ i:Axis4,∑ j:Axis4,(∫ x:R,w x * sep (m!-1) (F i j) x*(leg U L i [] x*leg V K j [] x))=0
   simp_rw [hr]; rw [sum_comm]; apply sum_eq_zero; intro j _
   rw [sum_comm]
   -- outer a then i then b : want b then a then i. two more
   have hg(j i:Axis4): (∑ b:Axis4,z*(V b j*U j i)*Q j b i j)= (∑ b:Axis4,z*(V b j*U j i)*Q j b i j):=rfl -- remove
   simp_rw [sum_comm (f:=fun i b=> _ * Q j b i _)]
   rw [sum_comm]; apply sum_eq_zero;intro b _
   rw [show (∑ a:Axis4,∑ i:Axis4,z*(V b j*U a i)*Q j b i a)=z*V b j*(∑ a:Axis4,∑ i:Axis4,U a i*Q j b i a) by simp only [mul_sum,mul_assoc], twist U hU (fun a i=>Q j b i a),mul_zero]; intro a c
   have hx:=spin hP j c a L (K++[b]) (by unfold score;simp;omega)
   simpa only [Q,F,List.cons_append,List.append_assoc] using hx

end YM.RG12.Strike
