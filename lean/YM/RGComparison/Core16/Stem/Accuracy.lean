import YM.RGComparison.Core16.Stem.Palm
/-! # No log debt at TOP SEAM output r+1. Tilt x call systematic.

This is BEFORE transfer for K columns and FRAME. Running coupling actual blueprint; AP allowance
tracking NOT using mandatory price R beyond previously declared outputs. Finite arity here.
Geometry uniform in p. Complement charged with span Amen Ω. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Fk
open Function Filter Set Lattice RG Tree Wilson MeasureTheory Metric Push.Uniform Forge
open PertExtension PertExtension.Series Tested Radial Therm Precision
open Planet Stage
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

section cash
variable {V U:Stage}{r:ℕ} {c:ℝ} {f : Cost} {y:Script}
omit V in
lemma date_purchase (U: Stage) : ∃ V:Stage,V.Above U ∧ ∀ x,V.L≤x→x^U.p*dollar x≤1:= by
   obtain ⟨V,h,-,hh⟩:= Lumen.clean U U.p ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero U.p).eventually (gt_mem_nhds zero_lt_one))
   exact ⟨V,h,fun _ hx=>(hh _ hx).le⟩
structure Allots (U: Stage)(s:Script) (r:ℕ)(C:ℝ) (f : Cost) :Prop where
    pos:0 ≤ C
    front (i:ℕ):i≤r→|s i|≤C
    earns (x:ℝ): U.L≤x→|f (dollar x) -peval s r (dollar x)| ≤ dollar x^(r+1)*C
lemma Allots.spends (h:Allots U y r c f) : Bill (r+1) (f-peval y r):=by
    refine ⟨c,h.pos,tollLess ?_⟩; filter_upwards [eventually_ge_atTop U.L] with s hs; exact ((h.earns s hs).trans_eq (mul_comm ..))
lemma peval_i j (g):untilB y (j+1) g= peval y j g:= rfl
lemma buy {U V:Stage}(h:V.Above U)(he:∀x,V.L≤x→ x^U.p*dollar x ≤ 1)(ht:U.Ticket (r+2) c (f ∘ dollar)) :
   ∃ D:Script,Allots V D r (2*c) f := by
    obtain ⟨a,ha,hA⟩:=ht.budgets; have hz:= ht.pos; refine ⟨a,by positivity,fun i hi=> (ha i (by omega)).trans (by linarith),fun x hx=>?_⟩
    let g:=dollar x; have hw:0<g:=dollar_pos _
    have hb' :U.rate c x (r+2) ≤ g^(r+1)*c:= by
       unfold rate; rw [pow_succ (dollar x)]; refine (show _ = x^U.p*g * (g^(r+1)*c) from by unfold g; ring) |>.le.trans (mul_le_of_le_one_left (by positivity) (he _ hx))
    refine (abs_sub_le (f g) (untilB a (r+1+1) g) _).trans (le_trans (b:=g^(r+1)*c+g^(r+1)*c) (add_le_add ((hA x (h.1.trans hx)).trans hb') ?_) ?_)
    · rw [← peval_i]; unfold untilB; rw [Finset.sum_range_succ]; have hs :dollar x=g:=rfl; rw [hs,add_sub_cancel_left,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤g^(r+1))]; gcongr; exact ha _ (Nat.lt_succ_self _)
    apply le_of_eq; unfold g; ring

lemma knows {z:Script}(h: Allots U y r c f)(he: Aspiration f z)(i:ℕ)(hi:i≤r) : y i=z i:=by
    let t j: ℝ:= if j ≤ r then -y j else 0
    have hp : Aspiration (peval (-y) r) t := Aspiration.polynomial (-y) r
    have hz : f+ peval (-y) r=f-peval y r:=by ext; simp [peval,Zone.eval,Finset.sum_neg_distrib]; ring
    have hh : (z+t) i=0:=(he.add hp).vanish (show Bill (r+1) (f+peval (-y) r) from hz.symm ▸ h.spends) (by omega)
    unfold t at hh; rw [Pi.add_apply,if_pos hi] at hh; linarith only [hh]
lemma Allots.replace {z:Script}(h:Allots U y r c f)(hv:∀ i≤r,y i=z i):Allots U z r c f:= by
    refine ⟨h.pos,fun i hi=>(hv i hi) ▸ h.front i hi,fun x hx=>?_⟩; rw [show peval z r (dollar x)=_ from (show peval y r (dollar x)=_ from Finset.sum_congr rfl (fun i hi=>by change _* y i=_*z i; rw [hv i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))])).symm]; exact h.earns x hx
end cash

variable {G:Gauge}{S:Side} {ι k L I T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D][Fintype L][Fintype A][Fintype I]
variable {X:Shelf G A D} {P: Planet X S ι k T} {Z: ChartRatio G}
variable (H:P.Steady) (hZ: LocalRatio Z) {f:Melody G ι} {p: Stuff G ι L} {ψ:(L→G.Color)→ℝ} {N a:ℕ}{C:ℝ} (hp:Visible X ψ f p N C)(h: Zeros a ψ)(he:ContDiffAt ℝ ω ψ 0)
-- actual normalized expectation estimator on this Wilson gas. Variables δean etc paid.
def baron (P:Planet X S ι k T)(f:Melody G ι)(a:ℕ)(g:ℝ):= g⁻¹^a*P.expect g (f g)
omit [Fintype D] [Fintype A] in
lemma translate (P:Planet X S ι k T)(f:Melody G ι)(a:ℕ) : reads P [] f a= (baron P f a) ∘ dollar:=by
    funext x; unfold baron reads comp; rw [Pi.mul_apply, show sing (G:=G) (ι:=ι) [] _=1 from rfl, one_mul]
include H hp he h hZ
lemma exterior : Aspiration (baron P f a) (read P Z p ψ a):=by
    have ht:= formula H hZ hp he
    refine ht.shift ?_; intro i hi; apply ht.vanish (w:=a) ?_ hi
    obtain ⟨U,j,hU,hv,hj,h⟩:= vintage H.prices ⟨1,0,le_rfl⟩ (fun (_:Unit)=>ψ) (fun _=> he.of_le le_top) 1 a 0 N ((abs_nonneg _).trans (hp.price _ (show amen X 0 from ⟨le_refl _, H.prices.thick.2.1.le⟩) 1))
    have hf:= h ι k T _ _ _ S P H () f p hp ‹Zeros a ψ› [] (Nat.zero_le 0) -- replace use C≥0 from H.env proof norm
    rw [translate] at hf
    obtain ⟨V,hV,hT⟩:=date_purchase U
    obtain ⟨D,hD⟩:=buy hV hT hf
    let M:= baron P f a
    have hB:Bill 0 M:= by rw [show M=M-peval D 0+peval D 0 from (sub_add_cancel ..).symm]; exact bill_add (bill_ge hD.spends (Nat.zero_le _)) (Aspiration.polynomial D 0|>.bounded)
    obtain ⟨d,hd,h⟩:= hB; refine ⟨d,hd,?_⟩; filter_upwards [h,Tested.eventually_pos] with i hi ht; rw [pow_zero,mul_one] at hi; refine le_trans (?_ : ‖_‖ ≤ ‖M i‖*i^a) (mul_le_mul_of_nonneg_right hi (by positivity)); unfold M baron; rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ i⁻¹^a),inv_pow]; field_simp; exact le_refl _
omit H hp he h hZ
include hZ
lemma projection (Y:Good X)(B:Stage)(ψ:I→ (L→G.Color)→ℝ)(hψ:∀ i,ContDiffAt ℝ ω (ψ i) 0) (r a N:ℕ)(hc : 0≤ C) : ∃ (T:Stage)(j:ℝ),T.Above B ∧ Visit T X ∧ 0≤ j ∧ ∀ (ι k U:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype U) (S:Side)(P:Planet X S ι k U),P.Steady→ ∀ i f p,Visible X (ψ i) f p N C→ Zeros a (ψ i) →Allots T (read P Z p (ψ i) a) r j (baron P f a):=by
    obtain ⟨U,c,h1,h2,h3,h4⟩:= vintage Y B ψ (fun i=> (hψ i).of_le le_top) (r+1) a 0 N hc; obtain ⟨V,hv,he⟩:= date_purchase U
    refine ⟨V,2*c,above_trans h1 hv, newer h2 hv,(by positivity),fun ι k T _ _ _ S P H i f p hp hh=> ?_⟩; have ht:=h4 _ _ _ _ _ _ S P H _ _ _ hp hh [] (Nat.zero_le _)
    rw [Fk.translate] at ht; obtain ⟨D,h⟩:= buy (r:=r) hv he ht; exact h.replace (knows h (exterior H hZ hp hh (hψ i)))
end YM.RGComparison.Core16.Lumen.Fk
