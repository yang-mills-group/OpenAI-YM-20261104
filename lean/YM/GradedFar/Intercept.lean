import YM.GradedFar.GaugeBook
/-!
# Independent first-order test ranks in the specified position book

Role in the G.1 bridge: lower Lipschitz/stability on actual small physical Change parameters,
while using the measured t on compact comparisons. Need use both D Position & the supplier
of the nontrivial connected thermometer coefficient (actually giving a signal on this horizon).
This supplies separation on BOTH the field change and measured t discrepancy **jointly**.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Billboard
open Function Filter Set PowerSeries MeasureTheory
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Menus
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Before" => Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Adj" => Scale.Measure.adjust (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "C⋆" => WilsonPrescription.criterion Z
variable {n h:ℕ}
local notation "V"=> Sec G h
local notation "Slot" => Toon G h
-- signal in the registered formal W_P book
include H
lemma lead0 (x:Stage n): Post h n x 0= iris x:= (H.separatedOPE 0).wilson.wardRank ..
lemma before0 (x:Stage n): Before h n x 0=iris x:=by
 have hb:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born
 exact Scale.Measure.dawn Z.scheme Z.criterion 0 M σ hG hb.Taylor hb.still hb.base n x
lemma adjustment (x:Stage n)(u:ListInput G n h) : Post h n x 1 u=Before h n x 1 u + Manifest.response x u (coeff 1 (Adj h)):=by
 have Hκ: coeff 0 (Adj h)=1:= ((H.details.toServed.toPosted.toQuoted.toContract.joint 0 h).2.2.scale).zero
 have hk:= Manifest.exhibits (Before h) (Adj h) 1 (i:=1) (fun n x=> before0 Z M H x) one_ne_zero Base.one (fun j hj=> by
    rw [show j=0 from (by omega),Hκ,Base.one.zero]) x u
 rw [Facets.acts_h,coeff_one,if_neg (by omega),show coeff 1 (Adj h)-0=coeff 1 (Adj h) from by ext1 y; exact sub_zero ((coeff 1 (Adj h)) y)] at hk; exact Eq.trans (sub_eq_iff_eq_add.mp hk) (add_comm ..)
local notation "bill"=> Reg.Faith.reports 0 C⋆ M h
lemma till_reports : Jury.Orders (Before h) bill:=by
 have hb:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born
 exact Jury.enrolled 0 M Z.scheme Z.criterion σ hG hb.Taylor hb.still hb.base
lemma signal_clear : (Z.store.measure h).D (bill 1) = 0:= by
 have H₀:= Tangent.unit
 have hb:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born
 have ht:= (Jury.solved (d:=h) 0 M Z.scheme Z.criterion σ hG hb.Taylor hb.still hb.base H₀.start H₀.real 1)
 rw [deck0,Normalize.author,rules] at ht; -- calculate substitute X degree1; concretely
 simp only [cut, ← Nat.range_succ_eq_Iic] at ht
 rw [Finset.sum_range_succ, Finset.sum_range_one] at ht
 simp at ht
 exact ht
-- position drift ℓ proportional to signal y forces A from D-equations only
lemma banal {y:ℝ}{A : V→ₗ[ℂ] V}(hp:A∈ Normalize.Change G h)
    (hf:∀ n (x:Stage n)(v:ListInput G n h), Manifest.response x v A =(y:ℂ)*Before h n x 1 v) : A=0:=by
 let a:Normalize.Change G h:= ⟨A,hp⟩; let T:= Z.store; have he: varies (reference G h) A= y • bill 1:=by
   ext1 n; ext1 t; ext1 v; change varies (reference G h) A n t v = (y:ℂ)*bill 1 n t v
   obtain h' := (till_reports Z M H (h:=h)).exact n 1 t v
   rw [measures_gradient,h']; let f(x:Points n):= Jury.fxt (Before h) x 1 v
   rw [show (y:ℂ)*t.applyTo f= t.applyTo (fun x=>(y:ℂ)*f x) from by unfold Test.applyTo; simp_rw [mul_left_comm _ (y:ℂ),integral_const_mul] ]
   apply Test.apply_eq; intro x hx; dsimp only [f]; rw [Jury.fxt,dif_pos hx]; exact hf _ (⟨x,hx⟩:Stage n) _
 change a.val=0; have hv:= Normalize.regular _ (T.prepared h) a; change (T.measure h).D (tang (stand (0:Normalize.Change G h)) _ _)=_ at hv
 rw [stand0, tangent] at hv; change (Z.store.measure h).D (varies _ A)=a at hv; rw [he,map_smul,signal_clear Z M H,smul_zero] at hv; exact
   congr_arg Subtype.val hv.symm

omit H
private lemma pulse_multiply {A B:Cn}(h:coeff 1 A=0)(hv:coeff 1 B=0):coeff 1 (A*B)=0:= by rw [coeff_mul]; simp [Finset.Nat.antidiagonal_succ,h,hv]
include H in
lemma signal : ∃ x:Stage 3, ∃ v:ListInput G 3 6, Before 6 3 x 1 v ≠ 0:= by
 by_contra! hf; obtain hv:= H.details.toServed.toPosted.toQuoted.toContract.meant
 have hp (x:Points 3): ∀ v:ListInput G 3 6, Jury.fxt (Before 6) x 1 v=0:= by
    by_cases h:x∈conf 3; intro v; rw [Jury.fxt,dif_pos h]; exact hf ⟨x,h⟩ v
    simp [Jury.fxt,h]
 have hh(x:Points 3) : coeff 1 (Select.Single (Before 6) x)=0:=by
    have ht(i:Rose.Badge): coeff 1 (Rose.batchT (Jury.fxt (Before 6) x) i)=0:=by rw [Rose.batchT,coeff_mk,hp]
    unfold Select.Single Rose.b3; simp_rw [map_add,map_sub,map_smul,ht Finset.univ];
    simp [pulse_multiply (ht _) (ht _),pulse_multiply (pulse_multiply (ht _) (ht _)) (ht _)]
 have h0:= congr_arg (coeff 1) hv; rw [Select.meter,Reg.Choice.tune,map_smul,map_sub, coeff_C,if_neg (by norm_num),show coeff 1 (X:PowerSeries ℂ)=1 from by simp,Select.output,coeff_mk] at h0
 simp_rw [hh] at h0; simp [Test.applyTo] at h0

-- Plan for h=6. slope along h<a; combine later.
include H in
theorem stampHigh {y:ℝ}{A: Sec G h→ₗ[ℂ] Sec G h}(hp:A∈ Normalize.Change G h)
    (HS:∃ x:Stage 3,∃ v:ListInput G 3 h, Before h 3 x 1 v ≠0)
    (hf:∀ n(x:Stage n)(v:ListInput G n h), Manifest.response x v A=(y:ℂ)*Post h n x 1 v) : A=0 ∧ y=0:=by
 let β:= coeff 1 (Adj h); have hx: β∈Normalize.Change G h:= (H.details.toServed.toPosted.toQuoted.toContract.joint 0 h).2.2.scale.high _ one_ne_zero
 let B:Normalize.Change G h:=⟨A,hp⟩; let α : Normalize.Change G h:=⟨β,hx⟩
 let f{n:ℕ}(x:Stage n)(v:ListInput G n h):= ((Manifest.response x v).restrictScalars ℝ) ∘ₗ (Normalize.Change G h).subtype
 have he(n)(x:Stage n)(v:ListInput G n h): f x v B=(y:ℂ)*(Before h n x 1 v+f x v α) :=
    (hf n x v).trans (congrArg ((y:ℂ)*·) (adjustment Z M H x v))
 have ha :B=y • α:=by
    apply sub_eq_zero.mp; apply Subtype.ext; refine banal Z M H (y:=y) ((B-y • α): Normalize.Change G h).property ?_; intro n x v
    change f x v (B - y • α) = _; rw [map_sub,map_smul, he n x v]; change (y:ℂ)*(_+_) - (y:ℂ)*_ =_; ring
 have hy:y=0:=by
    obtain ⟨x,v,hv⟩:= HS; apply Complex.ofReal_eq_zero.mp; apply (mul_right_inj' hv).mp; rw [mul_zero]
    specialize he 3 x v; rw [ha,map_smul] at he; change (y:ℂ)*f x v α=_ at he; linear_combination -he
 rw [hy,zero_smul] at ha; exact ⟨ congr_arg Subtype.val ha,hy⟩
include H in
theorem stamp {y:ℝ}{A: Sec G 6→ₗ[ℂ] Sec G 6}(hp:A∈ Normalize.Change G 6)
    (hf:∀ n(x:Stage n)(v:ListInput G n 6), Manifest.response x v A=(y:ℂ)*Post 6 n x 1 v) : A=0 ∧ y=0:=
 stampHigh Z M H hp (signal Z M H) hf
end YM.Integration.GradedFar.Tariff.Billboard
