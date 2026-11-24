import YM.AllOrder.Plateau.Lim
import YM.AllOrder.Plateau.Youth
/-!
# Exact restoration of physical E6 local norm in this housing, relative to curvature tape
 forecast. Sym.Free rotor compressed; leak budget on actual Haw.Hotel normalized.Output
 notch still PRE-RESET. Exposes stiffness stencil for curve process choices. Includes
 no perturbative regular family fake normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Plateau.Slim
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext Repeat Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush Poll ConnectedActivityE6.Coat
open Song AbsoluteSums AbsoluteSums.Animals Fare Shellac Work.G05
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G: Gauge} {n m q: Side} {k j w N : ℕ}
variable {σ C Z β x₀:ℝ} (p:BudgetPoint)
local notation "E"=>Positions (Primary n G)
open Trio Slide Marlin
section stamp
variable (C₁: Collection.Listing G n)(T:Collection.Source G n) (w v:ℕ)(f g t:Offer G n)
open Ovens Progress.DirectedRecipe Ovens.Pipes Refrain
local notation "Y"=> lodge C₁ w v
def blank (G:Gauge)(n:Side): Collection.Source G n:= ⟨0,0⟩
local notation "Ω"=> pluck p (lodge C₁ w v)
-- simpler letters
local notation "S0"=> bison T f t
local notation "S1"=> bison T (f-g) t
-- exposed Source projection identical for ANY cup: uses same alphabet, K supp unchanged
abbrev shadeT (f:Offer G n): ℕ→ Config G n→ℝ:= (bison (blank G n) f (fun _ => 0)).regular
variable {Q : ℕ→ Config G n→ℝ}
lemma tenor_book (hp: Meadow.Budget p (Marlin.leap (c:=n) w) g C): Meadow.Budget p (Marlin.lodge C₁ w v).reg (shadeT g) (turnFee p*C):= by rw [← zero_add (turnFee p*C)]; exact reg_bison C₁ w v (blank G n) g (fun _=>0) (Line.transparent C₁.reg) hp
lemma increase : (poursP p (lodge C₁ w v) S0).logRead - shadeT g = (poursP p (lodge C₁ w v) S1).logRead:= by
 funext i U; let y:=leanU n; let j: Door n→ Config G n→ℝ:=fun i U=>Song.Rim n*f i.2 (i.1.view U); let k':= choir g; change Sum.elim T.logRead j (y i) U - Sum.elim (fun _:ℕ=> fun _:Config G n=>0) k' (y i) U= Sum.elim _ (choir (f-g)) (y i) U -- PoursP actual
 cases y i with
 | inl k=> exact (sub_zero ..)
 | inr k=> exact (mul_sub (Song.Rim n) (f k.2 (k.1.view U)) _).symm
lemma rel (hp: Meadow.Budget p (Marlin.leap (c:=n) w) (f-g) C)(hz: Meadow.Budget p C₁.reg T.logRead Z): Meadow.Budget p (pluck p (lodge C₁ w v)).reg ((poursP p (lodge C₁ w v) S0).logRead - shadeT g) (Z+turnFee p*C):= by rw [increase]; exact reg_bison C₁ w v T (f-g) t hz hp
lemma shine_read (U:Config G n): (∑' i, masked p.threshold ((Ω).reg i|>.support) (shadeT g i) U)=∑ i:Site n, masked p.threshold (neighbors w i) (paid g i) U:= by
 let A:= fun i:Civ n=> Sum.elim (fun (_:ℕ) (_:Config G n)=> (0:ℝ)) (fun i:Door n => masked p.threshold (sea w i).support (choir g i)) i U -- binder issue
 have he i : A (leanU n i)= masked p.threshold ((Marlin.pluck p (lodge C₁ w v)).reg i|>.support) (shadeT g i) U:= by
    unfold A; change Sum.elim (fun _=> (0:Config G n→ℝ)) (fun i=> masked _ (sea w i).support (choir g i)) (leanU n i) U= masked p.threshold (Sum.elim C₁.reg (sea w) (leanU n i)|>.support) (Sum.elim (fun i:ℕ=> (0:Config G n→ℝ)) _ (leanU n i)) U; cases leanU n i with
    | inl i=> let X:Support n := (C₁.reg i).support; change (0:ℝ)=masked p.threshold X _ _; by_cases hU:Healthy p.threshold X U; rw [masked_eq _ _ _ _ hU]; rfl; rw [masked_ne _ _ _ _ hU]
    | inr i => rfl
 simp_rw [← he]; rw [(leanU n).tsum_eq,masked_slim p w g U,Summable.tsum_sum (f:=A) (show Summable (fun i:ℕ=>A (.inl i)) from summable_zero) Summable.of_finite]; erw [tsum_zero,zero_add]; exact tsum_fintype _ -- sum x Door convert
-- equivariance with SAME motion of original desk. Choose after mergest.Plucking.Beta. opacity gist.
variable (s:Signed)(b:Site n)
lemma stripes (u: Equiv.Perm ℕ) : ∀ i, shadeT f (congo (leanU n) (Marlin.reel s b u) i)= shadeT f i ∘ pull s b:= by
 intro i; let C := leanU n; let g:= congo C (Marlin.reel s b u); let z : Civ n→ Config G n→ℝ:= Sum.elim 0 (choir f); change z (C (g i))=z (C i) ∘ pull s b; rw [show C (g i)=Marlin.reel s b u (C i) from perch ..]; cases C i with | inl i=>rfl | inr i=> exact (spirit (Marlin.leap (c:=n) 0) f s b i).2.2
lemma walls (Y' : Listing G n)(X : Collection.Source G n) -- extend Moves.current Full requiring early C₁ support Motion; obtain forced any! for `kp`. Old C₁ means hp from HasLedger.moves.
    (hr:Y'.reg=(Marlin.pluck p (lodge C₁ w v)).reg) (he:X.logRead= (S0).regular)
    (H: (C₁.read T).Moves s b)(hp:(Y'.read X).Moves s b): ∃ M:(Y'.read X).Moves s b, ∀ i, shadeT g (M.ep i)= shadeT g i ∘ pull s b := by
   let L:= (lodge C₁ w v).reg; let y:=leanU n; let e:= Marlin.reel s b H.ep; let q:=congo y e; let f' := Sum.elim C₁.reg (sea w); let u:=Sum.elim T.logRead (Song.choir f);
   have hu:∀ i, (f' (e i)).support = (f' i).support.image (affine s b) ∧ (f' (e i)).site=affine s b (f' i).site∧ u (e i)= u i ∘ pull s b:= by
       rintro (i | i); exact ⟨H.reg_support i,H.reg_site i, funext (H.valuesE i)⟩; obtain ⟨hx,hp,hV⟩:=spirit (Marlin.leap (c:=n) w) f s b i; exact ⟨hp,hx,hV⟩
   refine ⟨⟨q,hp.kp,fun i=>?_,fun i=>?_,hp.forced_support,hp.forced_inventory,hp.forced_tests,fun i U=>?_,hp.valuesK⟩,stripes g s b H.ep⟩
   · change (Y'.reg (q i)).site=_; simp only [Listing.read] -- rewrite issue
     erw [hr]; change (f' (y (q i))).site=Lattice.affine _ _ (f' (y i)).site; rw [show y (q i)=_ from perch y e i]; exact (hu _).2.1
   · change (Y'.reg (q i)).support= (Y'.reg i|>.support).image (affine s b); rw [hr]; change (f' (y (q i))).support=(f' (y i)).support.image _; rw [show y (q i)=_ from perch y e i]; exact (hu _).1
   change X.logRead (q i) U=X.logRead i _; rw [he]; change u (y (q i)) U=u (y i) _; rw [show y (q i)=_ from perch y e i,(hu _).2.2]; rfl
end stamp
end YM.AllOrder.Plateau.Slim
