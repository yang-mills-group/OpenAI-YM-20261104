import YM.FormalBulk08.Spruce.Vote
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{X I J:Type}{W:Page X}{P:Pin W}{τ:Time X}{E e k:ℕ} {δ:X→ℝ}
section
-- unit wake has Jac. Nongrowth of highest coefficient as required.
variable (Q V:Pence)
def leavesR (n:ℕ):ℝ:=∑ j∈Finset.range n, coeff j Q * coeff n (V^j)
lemma peel (Q S:Pence)(h:Fresh S)(n): coeff n (Q.subst (PowerSeries.X*S))= coeff n Q + leavesR Q (PowerSeries.X*S) n:= by
    rw [subst_coeff (bottomless _) _ n n le_rfl,Finset.sum_range_succ, mul_pow]; rw [show coeff n (PowerSeries.X^n*S^n)=coeff 0 (S^n) from ?_, h.pow n,mul_one,add_comm]; rfl
    rw [mul_comm,coeff_mul_X_pow', if_pos le_rfl,Nat.sub_self]
end
variable [Fintype I][DecidableEq I]
-- entries row priority; decks growth ht. hc priority on U=already inverse.
lemma momentum {f:Deck P→ℝ}{A B: Turn P→ Pennants I}{s r:I→ℕ}{κ:Turn P→ I→ℝ}{T V: Turn P→Pence}{S Q: Deck P→ Matrix I J Pence}{D M:Turn P→Matrix I J Pence}(p:∀ i,Found s r (A i) (κ i))(hv:∀ i, Found s r (B i) (κ i))(ht:∀ i j,κ i j≤1)(hc:∀ i, S (startP i P)=0)(hs:∀ i,Q (startP i P)=0)
    (h:∀ i:Turn P,S i.ups=(A i*(D i+S i.bed)).map (PowerSeries.subst (PowerSeries.X*T i))) (hz:∀ i:Turn P, Q i.ups=(B i*(M i+Q i.bed)).map (PowerSeries.subst (PowerSeries.X*V i)))(hT:∀ i,Fresh (T i))(hV:∀ i,Fresh (V i))(hb:Soft τ (fun i=>(steps P i:ℝ)))(hδ:∀ i,0≤δ i)(hf:∀ i,0≤f i)(ha:∀ i:Turn P, f i.bed≤ f i.ups)
    (hm:∀ i j, Priced (qday τ P) (fun i=>δ i.a) (fun x=>A x i j) (fun x=> B x i j) E)(hp: Priced (qday τ P) (fun i=>δ i.a) T V E)(hq: ∀ i j e, e≤ E→ Calm (qday τ P) (fun i=>δ i.a) (fun i=>f i.ups) (fun x=> coeff e (D x i j)) (fun x=>coeff e (M x i j))):
       ∀ j (k:J) e, e≤ E → Calm (rday τ P) (fun i=>δ i.a) f (fun i=> coeff e (S i j k)) (fun i=>coeff e (Q i j k)):= by
    intro j k e he; induction e using Nat.strong_induction_on generalizing j with
    | _ e ih=>
       let u:=priority s r;let t:= ∑ i,u i; have hg i:u i≤ t:= Finset.single_le_sum (f:=u) (fun _ _=>Nat.zero_le _) (Finset.mem_univ _)
       generalize hU:t-u j=n
       induction n using Nat.strong_induction_on generalizing j with
       | _ n h₁=>
          let C (X:Pennants I)(S:Matrix I J Pence)(_p:ℕ)(x:I × ℕ × ℕ):= coeff x.2.1 (X j x.1)*coeff x.2.2 (S x.1 k)
          let X1(p:ℕ):= (Finset.univ:Finset I) ×ˢ Finset.antidiagonal p; let y:I×ℕ ×ℕ:= (j,0,e); let d:= (X1 e).erase y
          let X'(P:Pennants I)(D S:Matrix I J Pence):=P*(D+S);let P'(x:Turn P):=X' (A x) (D x) (S x.bed);let U x:=X' (B x) (M x) (Q x.bed)
          have hA (X:Pennants I)(S:Matrix I J Pence)(p:ℕ): coeff p ((X*S) j k)=∑ i ∈ X1 p,C X S p i:=by rw [Matrix.mul_apply,map_sum, Finset.sum_product]; exact Finset.sum_congr rfl fun i _=> coeff_mul ..
          let R(Z:Pennants I)(D S:Matrix I J Pence)(V:Pence):= (∑ i∈X1 e,C Z D e i)+(∑ i∈d,C Z S e i)+ leavesR (X' Z D S j k) (PowerSeries.X*V) e
          have hh (Z:Pennants I)(b:I→ℝ)(D S:Matrix I J Pence)(V:Pence)(hp:Fresh V)(h:Found s r Z b): coeff e ((X' Z D S j k).subst (PowerSeries.X*V))= b j * coeff e (S j k)+ R Z D S V:=by rw [peel _ _ hp e, show coeff e (X' Z D S j k)= coeff e ((Z*D) j k)+coeff e ((Z*S) j k) by rw [show X' Z D S=Z*D+ Z*S from Matrix.mul_add .., Matrix.add_apply,map_add],hA Z D,hA Z S,← Finset.add_sum_erase (X1 e) (C Z S e) (show y∈ X1 e from Finset.mem_product.mpr ⟨Finset.mem_univ _,by simp [y]⟩),show C Z S e y=b j* coeff e (S j k) from congr_arg (·* coeff e (S j k)) (h.due _)]; unfold R d;ring
          have hT (i):coeff e (S i.ups j k)= κ i j * coeff e (S i.bed j k) + R (A i) (D i) (S i.bed) (T i):= by rw [h i]; exact hh _ _ _ _ _ (hT i) (p i)
          have hZ i:coeff e (Q i.ups j k)=κ i j * coeff e (Q i.bed j k)+ R (B i) (M i) (Q i.bed) (V i):= by rw [hz i]; exact hh _ _ _ _ _ (hV i) (hv i)
          refine coral_clock hf ha hδ (fun i=>κ i j) (fun x=>by rw [abs_of_pos ((p x).scale _)]; exact ht _ _) (fun i=>by rw [hc,Matrix.zero_apply,map_zero]) (fun i=>by rw [hs,Matrix.zero_apply,map_zero]) hT hZ ?_ hb
          let f'(x : Turn P):= f x.ups; let δ' (x:Turn P):=δ x.a; let τ':= qday τ P
          have hI k' i (h:k'<e): Calm τ' δ' f' (fun x=>coeff k' (S x.bed i k)) (fun x=>coeff k' (Q x.bed i k)):= ((ih k' h i (h.le.trans he)).lifted Turn.bed τ' (soft_day τ')).lapse ha (fun i:Turn P=>hδ _)
          have hJ (q)(hq':q≤e) : Calm τ' δ' f' (fun x=> coeff q ((A x* D x) j k)) (fun x=>coeff q ((B x*M x) j k)) := by
             simp_rw [hA]; apply calm_sums _; rintro ⟨v,i,z⟩ hz; have hv:i+z=q:=Finset.mem_antidiagonal.mp (Finset.mem_product.mp hz).2; exact (hq v k z (by omega)).growth (hm j v i (by omega))
          have hx1: Calm τ' δ' f' (fun x=>∑ i∈X1 e,C (A x) (D x) e i) (fun x=>∑ i∈ X1 e,C (B x) (M x) e i):=by simp_rw [←hA]; exact hJ _ le_rfl
          have hx2 : Calm τ' δ' f' (fun x=>∑ i∈d,C (A x) (S x.bed) e i) (fun x=>∑ i∈d,C (B x) (Q x.bed) e i):= by
             apply calm_sums; rintro ⟨v,q,o⟩ ho; have h':=Finset.ne_of_mem_erase ho; have hq:q+o=e:= Finset.mem_antidiagonal.mp (Finset.mem_product.mp (Finset.mem_of_mem_erase ho)).2
             by_cases hp:o<e
             · exact (hI o v hp).growth (hm j v q (by omega))
             have hh:q=0:=by omega
             have hx:o=e:=by omega
             subst q o; by_cases hQ:u j<u v
             · have hy:t-u v<n:=by have H:=hg v;omega
               exact (((h₁ _ hy v rfl).lifted Turn.bed τ' (soft_day τ')).lapse ha (fun i: Turn P=> hδ _)).growth (hm j v 0 (Nat.zero_le _))
             have hv':j≠v:=fun z=>h' (Prod.ext z.symm rfl)
             simp_rw [show ∀ i,C (A i) (S i.bed) e (v,0,e)=0 from fun i=>mul_eq_zero.mpr (Or.inl (show coeff 0 (A i j v)=0 from Classical.byContradiction fun ht=> hQ (promotes ((p i).min j v ht hv')))), show ∀ i,C (B i) (Q i.bed) e (v,0,e)=0 from fun i=> mul_eq_zero.mpr (Or.inl (show coeff 0 (B i j v)=0 from Classical.byContradiction fun ht=>hQ (promotes ((hv i).min j v ht hv')))) ]; exact Calm.quiet ..
          refine Calm.sum (hx1.sum hx2) ?_; unfold leavesR; apply calm_sums _; intro i hi; rw [Finset.mem_range] at hi; have hX:= (transit hp|>.le (Nat.le_succ _)).pows i
          have hY(k')(hx:k'<e): Calm τ' δ' f' (fun x=>coeff k' (P' x j k)) (fun x=> coeff k' (U x j k)) := by unfold U P' X'; simp_rw [Matrix.mul_add,Matrix.add_apply,map_add]; apply Calm.sum (hJ k' hx.le); simp_rw [hA]; apply calm_sums _;rintro ⟨v,m,n⟩ hn; have ht:m+n=k':=Finset.mem_antidiagonal.mp (Finset.mem_product.mp hn).2; exact (hI n v (by omega)).growth (hm j v m (by omega))
          convert (hY i hi).growth (hX e he) using 1 <;> ext <;> rw [mul_comm]
end YM.FormalBulk08.Spruce
