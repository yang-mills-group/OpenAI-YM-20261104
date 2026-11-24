import YM.MS.Mach.Mark
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Plate
/-!
# Word recipes to full polynomials. Sky.A neutral.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Rock Path Oceans
-- keep Grid.P `Lifting`
open _root_.YM.MS.Shine Hem Mell Motif Literal Halo Alps Native Outlook High Detect Lifting
open scoped Topology ContDiff InnerProductSpace
variable {J:Type}{G:Gauge} {k m n:ℕ}{b:Bool}{z:ℂ}{F H:Rack G n}{x y:ℝ→ Rack G n}{U Y:Mield G n}
local notation "Ψ"=> field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄"=> product Ψ
namespace Pole
variable (k) (f:Fin k→Plaq) (σ:Grid G k)
lemma turn_t (P:Surf G m n)(hv:P.keeps) : P.run ( wing k f σ z n )= wing k f σ z m:= by
   induction k with| zero=> exact P.fixC 1| succ k ih=> change P.run ( bite n G _ (wing k (f∘Fin.succ) (σ∘Fin.succ) z n))= _; rw [P.prod,ih]; congr 2; exact congr_fun (Pole.v_wall (f 0).i (f 0).j (f 0).jets P hv) (σ 0) -- rfl simplification?
lemma passage (i:Plaq): ( Grit i:ℤ)= i.value := by simp only [Grit,Plaq.value, Nat.cast_add,Nat.cast_ofNat]
lemma payZ : (wage k f:ℤ) =∑ i:Fin k,(f i).value:= by simp_rw [wage,Nat.cast_sum,passage]
lemma PaceV (hx:star z=z): Pace ( wing k f σ z n ) (wage k f) 0 (wage k f):= by
    induction k with
    | zero=> simp_rw [wage,Fin.sum_univ_zero, Nat.cast_zero]; exact Pace.unit
    | succ k ih=> rw [wage_add,Nat.cast_add, Grit, Nat.cast_add,Nat.cast_ofNat]; exact Pace.times (Pole.cap (G:=G) (n:=n) (f 0).i (f 0).j (f 0).jets hx (σ 0)) (ih (f∘Fin.succ) (σ∘Fin.succ)) -- after rw Grit maybe mismatch
lemma size0 : Book.rank k (wing k f σ 0 n):= by
   induction k with| zero=> exact Rails.coin 1| succ k ih=> rw [Nat.cast_add,Nat.cast_one,add_comm _ (1:ℤ)]; exact (Pole.rank0 (n:=n) (f 0).i (f 0).j (f 0).jets (σ 0)).product (ih (f∘Fin.succ) (σ∘Fin.succ))
lemma read0 : wing k f σ 0 0= family k ( Plaq.mark ∘ f ) σ:= by
   induction k with
   | zero=> rfl
   | succ k ih=> unfold family wing; rw [prodS, show ∀ a:Plaq, Pole_leaf (n:=0) 0 a (σ 0)= Koszul.mono (a.mark (σ 0)) from fun a=> Pole.singleM a.i a.j a.jets _, Local.glow_add]; exact congr_arg ((bite 0 G) (Koszul.mono ((f 0).mark (σ 0)))) (ih (f∘Fin.succ) (σ∘Fin.succ)) -- universe
-- same quote.H.Prop. center. 
lemma angel (n:ℕ)(u:G.El) : repeatC u (saint k f σ z n)= saint k f σ z n := by
   simp_rw [saint, Finset.sum_apply,Pi.smul_apply]; exact Lifting.cash (R:=ℂ) (fun i=> wing k f i z n) u (P:= Color.repeatC u) (fun i=> radiant k f i u) σ
lemma presence : Present (saint k f σ):= Present.sum _ (fun i _=> (Presence k f i).smul _) -- Expected .quote.Higher
lemma apric : Sturdy false (saint k f σ z) := by
   have hv {m n} (A:Surf G m n)(h:A.keeps): A.run (saint k f σ z n)= saint k f σ z m := by simp_rw [ saint, Finset.sum_apply, Pi.smul_apply, map_sum,map_smul, turn_t k f _ A h]
   -- `m n` generalize auto implicit already fixed in lemma? need ∀
   refine ⟨fun i X h=> hv (Surf.orbit X G) (Surf.orbit_s X h),fun i x=> congr_fun (hv (Surf.border G i) (Surf.border_s i G)) x ⟩
lemma reality (hx:star z=z): Pace (saint k f σ z n) (wage k f) 0 (wage k f):= by simp_rw [saint,Finset.sum_apply, Pi.smul_apply]; exact Pace.total _ (fun i _=> (PaceV k f i hx).cash (by simp))
lemma fare : Book.rank k (saint k f σ 0 n):= by simp_rw [ saint, Finset.sum_apply,Pi.smul_apply]; exact Rails.sum _ (fun i _=> (size0 k f i).smul _)
lemma y_floor : saint k f σ 0 0= breeze (family k ( Plaq.mark ∘ f )) σ:= by unfold breeze; simp_rw [saint, Finset.sum_apply, Pi.smul_apply, read0]
lemma real_h : Safe (saint k f σ z n) z:= by simp_rw [saint,Finset.sum_apply, Pi.smul_apply]; exact Safe.total _ (fun i _=> (prepared k f i).cash _)
end Pole
end YM.MS.Mach
