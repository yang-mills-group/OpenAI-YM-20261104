import YM.FVA2.Main
import YM.SignedWilsonExpansion.F9.Table
/-!
# Position tangent injective at prescribed frame including coupling.Rotation spin H required.

Use all fields through same `(d≥6)` and consequence of the actual Recipe. Then crop tests.
-/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SignedWilsonExpansion.Commission
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open FVA2 FVA2.Arrival FVA2.Main FVA2.Scale FVA2.Position FVA2.Position.Axes
open scoped Topology ContDiff BigOperators Classical
-- orient independently.Require Mission hypothesis supplied. `'phase' → Gram.Face.p.`.
open WilsonCoeffUV.Mer.Xa
variable {G:Gauge}{n d i l:ℕ}{σ:Type}
variable (N : Register.WilsonPrescription G) (h : G.Simple)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (S : Prescription (Press.portDeck G)) {dial: Bool}
variable (ν:ℝ) (P:Match N h T S dial)
open Jury Reg
-- Mass.MS coordinate convention registration only; budget on σ. Clock etc through head.
abbrev TPoint (G:Gauge)(d:ℕ):= (↥(Normalize.Change G d)) × ℝ
-- Grounded type failure `:Type` coercion? use `(Change...)`
abbrev earPoint (T:Tape.Table (Sec G d) n)(p:Tags G d n) (M:TPoint G d): ℂ:= (M.2:ℂ)* T 1 p+ ∑ i,T 0 ( update p i (M.1.val (p i)) )
namespace Method
variable (W:Initialize G){P':Normalize.Store G}(K:Rose.Pick P') (M:Scale.System.Contract W K T S)
local notation "Y"=> Measure.start W K d
local notation "B"=> Measure.start W K 6
include M h
-- derive position input
lemma ears (x:Points n)(p: x∈conf n)(k:ℕ)(t:Tags G d n): Tendsto (fun y:Sample n=> Rose.measureₓ W K d y k t) (Gate x) (𝓝 ((Y) n ⟨x,p⟩ k t)):=by obtain ⟨hs,hr,hu⟩:= M.toMission.toSchemeV.born; exact (Measure.together W K 0 T S h hs hr hu _ ) ▸ Measure.reaches W K 0 T S h hs hr hu d n ⟨ x,p⟩ k t -- syntax
lemma orderd0 : Equator.StarGround (Y):=by obtain ⟨hs,hr,hu⟩:= M.toMission.toSchemeV.born; exact Measure.dawn W K 0 T S h hs hr hu
lemma orderd (a b:ℕ) (v:a≤b): Inherited ( Measure.start W K a ) ( Measure.start W K b ) v:= by obtain ⟨hs,hr,hu⟩:= M.toMission.toSchemeV.born; exact Measure.inherited W K 0 T S h hs hr hu v
lemma official : Orders (Y) (Reg.Faith.reports ν K T d):= by obtain ⟨hs,hr,hu⟩:= M.toMission.toSchemeV.born; exact Jury.enrolled ν T W K S h hs hr hu
lemma washed (i:ℕ)(p:i≠0): (P'.measure d).D (Reg.Faith.reports ν K T d i)=0:=by
    obtain ⟨hs,hr,hu⟩:= M.toMission.toSchemeV.born
    let Q:= Reg.Faith.reports ν K T d
    have hv:= Jury.solved ν T W K S h hs hr hu (p:=PowerSeries.X) (d:=d) (show Rooted X from by simp [Rooted]) (PowerSeries.map_X _) i; rw [if_neg p, deck0, Normalize.author] at hv; rw [← hv]; apply congr_arg; symm; rw [rules,Finset.sum_eq_single i]; · rw [Program.cut,coeff_X_pow,if_pos rfl,one_smul];
    · intro b _ h; unfold Program.cut; simp only [coeff_X_pow,if_neg (Ne.symm h)]; exact zero_smul ..
    simp
-- pair price, tangent coupling.Temperature φ.Code
lemma impetus : ∃ x:Stage 3, B 3 x 1 (Rose.tag G) ≠ 0:=by
   by_contra! v; have hv : Select.meter K (B)=_:= M.meant; have he:= congr_arg (coeff 1) hv; rw [ Select.meter,Reg.Choice.tune,map_smul,map_sub, coeff_C,if_neg (by decide),Select.output,coeff_mk ] at he
   rw [show Test.applyTo _ _=0 from (?_), sub_self,smul_zero,coeff_one_X] at he; exact zero_ne_one he
   let f:= Rose.test K; refine Eq.trans (Test.apply_eq (f:=f) (P:=0) (?_)) (by simp [Test.applyTo]); intro x hx; change coeff 1 (Rose.b3 ( Rose.batchT ( fxt (B) x ) )) = 0; rw [ fxt,dif_pos hx,Rose.tangent W h _ (orderd0 h T S W K M 3 ⟨x,hx⟩ ) hx]; exact v ⟨x,hx⟩
lemma independence (u:6≤d)(i:TPoint G d)(p:∀ n (x:Stage n)(v:Tags G d n), earPoint ((Y) n x) v i=0): i=0:=by
    let G':=Y; let H:= 0; let P:ℕ→ Prediction G d:= Reg.Faith.reports (0:ℝ) K T d; have H':= official h T S 0 W K M (d:=d); let x':=(i.1:Normalize.Change G d); let b:= (i.2:ℂ); let A:= (i.2 • P 1)+gradient G d i.1
    have hv:A=0:=by
        ext1 n; ext1 t; ext1 v; change i.2 • P 1 n t v+ varies (reference G d) i.1.val n t v = 0
        rw [measures_gradient,H'.exact]; rw [Complex.real_smul]; let U(q:Points n):= ∑ j, scene q d (update v j (i.1.val (v j)))
        let K(q:Points n):= fxt G' q 1 v; let e(q:Points n):=b*K q; change b*(Test.applyTo t K)+Test.applyTo t U=_; rw [show b*(Test.applyTo t K)= Test.applyTo t e from (by unfold Test.applyTo e; simp_rw [mul_left_comm (t _) b]; rw [integral_const_mul])]
        have hP (x:Points n)(p':x∈conf n): e x+U x=0:=by
           have hg:= p n ⟨x,p'⟩ v; unfold earPoint at hg; rw [orderd0 h T S W _ M n ⟨x,p'⟩] at hg; unfold e K; rw [fxt,dif_pos p']; exact hg
        have hx(i:Points n): t i*e i+t i*U i=0:=by rw [←mul_add]; exact if p:i∈conf n then (by rw [hP i p,mul_zero]) else (by rw [Test.vanishes t p,zero_mul])
        unfold Test.applyTo; rw [← integral_add (t.smearing (ContinuousOn.const_mul (H'.light n 1 v) b)) (t.smearing (continuousOn_finsetSum _ (fun i _=> smooths _)))]; change (∫ i:Points n, t i*e i+t i*U i) = _; simp_rw [hx]; simp
    have hv0:i.1=0:=by
        have hc:=congr_arg (P'.measure d).D hv; rw [ map_zero ] at hc; unfold A at hc; rw [map_add,map_smul,washed h T S (ν:=0) W K M 1 (by decide),smul_zero,zero_add] at hc; exact ((P'.prepared d).1 i.1).symm.trans hc
    obtain ⟨x,v⟩:= impetus h T S W K M; let t:= up u ∘ Rose.tag G; have hc:= p 3 x t; unfold earPoint at hc; rw [hv0, Submodule.coe_zero] at hc
    have hy:∀ j: Fin 3, (Y) 3 x 0 (update t j 0)=0:=fun j=> MultilinearMap.map_coord_zero _ (i:=j) (Function.update_self ..); simp_rw [LinearMap.zero_apply,hy, Finset.sum_const_zero,add_zero] at hc; rw [← Method.orderd h T S W K M 6 d u 3 x 1 (Rose.tag G)] at hc; exact Prod.ext hv0 ( Complex.ofReal_eq_zero.mp ( (mul_eq_zero.mp hc).resolve_right v))
end Method
end YM.SignedWilsonExpansion.Commission
