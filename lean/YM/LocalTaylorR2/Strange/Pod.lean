import YM.LocalTaylorR2.Strange.Claim
import YM.LocalTaylorR2.Reel.Thicket
/-! # Transport argument-Taylor on the overridden E chart.
 All fields except E (including calibration parameters) retained. Called
 with arbitrary inheriting Reel.Scroll, and delivered on only Affords. In the
 true law the hard sectors/labels are read unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Strange
open Exponent
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Brim
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}
open YM.RG01.Survive Port Candle
open Reel Mesh
structure Engine (G:Gauge) extends Observatory G where
  plug : ∀ {c f L : Side}{S:StepData c f}{T:Tube G S}{R:Rep G f}{P:Teller G}{Q:YM.ConnectedActivityE6.Target G P}{W x μ C:ℝ}{o:Target.Order G W}, Cash W x μ L Q o C T R → Reel.Scroll G f → ℕ → LogIndex c f → Port.Test T
  fits : ∀ {c f L : Side}{S:StepData c f}{T:Tube G S}{R:Rep G f}{P:Teller G}{Q:YM.ConnectedActivityE6.Target G P}{W x μ C:ℝ}{o:Target.Order G W} (H:Cash W x μ L Q o C T R) (E: Reel.Scroll G f)(J:Cash W x μ L Q o C T (bend R E)) (p:ℕ), plug H E p = toObservatory.upgrade J p
variable (Ξ:Engine G) (E:Reel.Scroll G f)
def ovens {p:Molecule S}{l:ℕ}(q:Paint p l):Port.Test T:= fun F X w=> ∏ i : ↥(logs p), (Ξ.plug H E l i.val F X w)^Series.rank (q i) / ((Series.rank (q i)).factorial:ℝ)
def flaming {l:ℕ} : Expansions H l:=fun p q V=> if live H p then convolve (U:=p.val) q (fun i=> episode H χ p.val (ovens H Ξ E i) V) else 0
lemma uplift {p:Molecule S}{l:ℕ}(J:Cash W s μ L Q o C T (bend R E))(q:Paint p l)(hh: chooseSlot q ≠ perch l): ovens H Ξ E q=Mesh.warm J (Ξ.upgrade J l) q:=by
  unfold ovens warm; rw [Ξ.fits H E J l]; funext F X z; apply prod_congr rfl; intro i _; exact (Mesh.lights hh _ _ _).symm
lemma empanel {l:ℕ} (J:Cash W s μ L Q o C T (bend R E))(p:H.ThinP)(q:Orders l)
    (Y:J.ThinP)(h:Y.val=p.val)(hq:q.val ≤ l): flaming H Ξ (χ:=χ) E p q = Mesh.issue J (Ξ.upgrade J l) χ Y q:=by
  have hu : q≠ Candle.perch l:=fun he=> by rw [he, Candle.perch] at hq; rw [Fin.val_last] at hq; omega
  funext z; rw [Mesh.issue,if_neg hu]; unfold flaming Mesh.ode
  rw [← admissible H J rfl rfl rfl _ _ h]
  split
  · generalize_proofs
    rw [h]; unfold convolve; apply Finset.sum_congr rfl; intro i hi
    dsimp only; rw [uplift H Ξ E J i (by rw [(mem_filter.mp hi).2]; exact hu)]; exact congr_fun (pasture H J rfl rfl rfl p.val _) z
  rfl
variable {I₁:Cash W s μ L Q o C T R'} (X: Alliance I₁ H 1 0)
lemma envois {l : ℕ} (J:Cash W s μ L Q o C T (bend R E))(u:Alliance H J 1 0)(hu:u.units=Equiv.refl _)
    (Z: H.fragrances)(V: Config G c)(F:ℕ → Prop)(hF:∀ i, F i→ i≤l): fullSegments (fun _ i=>F i) (flaming H Ξ E (l:=l) (χ:=χ)) Z V= fullSegments (fun _ i=>F i) (Mesh.issue J (Ξ.upgrade J l) χ (l:=l)) (u.furrow Z) V:= by
  unfold fullSegments; rw [Match.weighs u.bearing u.sec Z]; congr 1
  apply Finset.sum_congr rfl; intro i hi; unfold aliquot
  apply prod_congr rfl; intro q hq; apply congr_fun; apply empanel H Ξ E J (Z.2 q)
  · change u.units _=_; rw [hu]; rfl
  exact (le_trans (single_le_sum (f:=fun j=> (i j).val) (fun _ _=>Nat.zero_le _) (mem_univ q)) (hF _ (mem_filter.mp hi).2))
def ebony (χ : Chi) (γ:ℝ)(p:ℕ)(φ:Bool)(f:ℕ→Prop): Magazine I₁ → Config G c→ℝ:= Sum.elim
      (fun i=> (-1:ℝ) • fullSegments (M:=p) (fun _ q => f q) (flaming H Ξ E (χ:=χ)) (X.furrow i))
      (fun (i : Songbook c)=> (if φ then (1:ℝ) else 0) • opus I₁ X χ γ (Sum.inr i))
def comet (χ : Chi) (γ:ℝ)(p:ℕ)(φ:Bool)(f:ℕ→Prop):= choir (ebony H Ξ E X χ γ p φ f) ∘ pennant I₁

lemma ebon {l:ℕ} (p:ℕ→Prop)(χ:Chi)(γ:ℝ)(Rz:Bool){I₂:Rep G f} (I':Cash W s μ L Q o C T I₂) (T:Alliance I₁ I' 1 0)(x:Expansions I' l)(hk:R.beta=I₂.beta)
   (hh:∀ i:I₁.fragrances,fullSegments (fun _ j=>p j) (flaming H Ξ E (l:=l) (χ:=χ)) (X.furrow i)=fullSegments (fun _ j=>p j) x (T.furrow i)):
    comet H Ξ E X χ γ l Rz p=(cohort I' (χ:=χ) T γ x Rz p).logRead:=by
    dsimp only [comet,ebony,cohort,opus,Sum.elim_inr]; simp_rw [hh,hk]
lemma heal (J:Cash W s μ L Q o C T (bend R E))(T:Alliance I₁ J 1 0)(ht:T.units=Equiv.refl _)(hx:X.units=Equiv.refl _)(χ:Chi)(γ:ℝ)(p:ℕ)(φ:Bool)(f:ℕ→Prop)(he:∀ i,f i→ i ≤ p): comet H Ξ E X χ γ p φ f=(cohort J («χ»:=χ) T γ (Mesh.issue J (Ξ.upgrade J p) χ) (M:=p) φ f).logRead:= by
   apply ebon H Ξ E X _ _ _ _ J T _ rfl
   intro i; funext V; let L:Alliance H J 1 0:= Match.staple rfl rfl rfl
   rw [← Yearling.trappings X L T hx rfl ht i]; exact envois H Ξ E J L rfl (X.furrow i) V f he
end YM.LocalTaylorR2.Strange
