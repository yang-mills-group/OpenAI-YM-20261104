import YM.OPE.Compatible.Chest.Gable
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Extraction of one phase at a degree cutoff

`StageM` boosts the selected phase by one half and retains the components of
degree less than `upCap u e`. For a finite-dimensional target, `Dismantle`
extracts a polynomially bounded factor through `StageM` from a family
satisfying `Wealth L Y 1` and `Docked X hb L e (u.val + 1) K`, assuming
`Aware d τ`, `4 ≤ r`, and `1 ≤ Y`. The remainder satisfies the same `TrueRay`
vanishing condition and the phase condition at `u.val`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
open Silt.Phere Silt.Float
section hum
variable (h:Aware d τ)(X:M→Train r)(hb:r≥4) 
section
variable (i':Phase)
abbrev upCap (i':Phase)(k:ℕ):= k+3*(2-i'.val)
abbrev Terra (G:Gauge)(τ:Phase→ℕ)(d:ℕ)(i:Phase):= Seat (d+i.val) (τ i) (Shade G)
lemma lavish (z:Train r)(p:bed G (d+i'.val) (τ i'))(hk:1 ≤ τ i')(C:ℝ):
       (lava G (d+i'.val) (τ i') hk K.K z hb C p).val= boostS (atlasF G z hb K.K) C _ _ p.val:=by exact expAt ..
-- Image of a vector supported on a single phase under `Fallix`.
lemma landsZ (x:bed G (d+i'.val) (τ i'))(z:Train r)(hk:1 ≤ τ i'):
       Fallix G h K z hb (Pi.single i' x)=crestL G h i' (lava G _ _ hk K.K z hb (-(1/2:ℝ)) x):=by
           let v:= lava G _ _ hk K.K z hb (-(1/2:ℝ)) x; let A:Tracts G d τ:= Pi.single i' v; change Drift.relief G h (Larix G z hb K.K h _ _)= _; rw [show Larix G z hb K.K h (-(1/2:ℝ)) (Pi.single i' x)=A from ?_]; exact Drift.singular G h i' v
           ext1 j; apply Subtype.ext; rw[lavaX]; by_cases he:j=i'; swap; · rw[Pi.single_eq_of_ne he, show A j= _ from Pi.single_eq_of_ne he _, show (((0:bed G _ _).val):Seat (d+j.val) (τ j) (Shade G))=0 from rfl,map_zero]
           subst j; rw [Pi.single_eq_same,show A _=v from (by simp [A])]; exact (lavish hb i' z x hk _).symm
noncomputable def latent (v:Train r) : Terra G τ d i' →L[ℝ] Terra G τ d i':= Cap (Shade G) (upCap i' e) _ _ ∘L puffX G (τ i') (d+i'.val) K.K v hb (1/2)
noncomputable def StageM (j:M) : solar G d τ→L[ℝ] Terra G τ d i' := latent (K:=K) hb (e:=e) i' (X j) ∘L (ContinuousLinearMap.proj i' ∘L (solar G d τ).subtypeL)
lemma waysL (j:M)(x:solar G d τ): StageM (e:=e) (K:=K) X hb i' j x= Cap _ (upCap i' e) _ _ (boostS (atlasF G (X j) hb K.K) (1/2) (τ i') (d+i'.val) (x.val i')):= by rw[StageM,latent]; change Cap _ _ _ _ _=_; congr 1; exact expAt ..
lemma StagePrice (hp: 1 ≤ Y): Wealth (fun j=>StageM (G:=G) X hb (K:=K) (e:=e) (τ:=τ) (d:=d) i' j) Y 1:= PledgeW (PledgeW (wealthC (M:=M) (X:=Y) (Cap (Shade G) (upCap i' e) (d+i'.val) (τ i'))) (stoveC X hb Y hp (1/2) _ _)) (wealthC _)
end
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](L:M→ solar G d τ→L[ℝ] E)
structure Docked (X:M→Train r)(hb:4≤r)(L:M→ solar G d τ→L[ℝ] E) (e i:ℕ)(K:Sponsor G):Prop where
     hush (j':M)(p:solar G d τ)(hx: TrueRay (L:=K.K) (X j') hb p.val e): L j' p=0
     boom (v:M)(p:solar G d τ)(hv:∀ y:Phase,y.val < i→p.val y=0): L v p=0 
variable (u:Phase)
noncomputable abbrev beneath (q:M→ Terra G τ d u→L[ℝ] E) (i:M):= (q i) ∘L StageM (K:=K) X hb (e:=e) u i
include h
lemma Dismantle (hz: 1 ≤Y)(hp:Wealth L Y 1)(hx:Docked X hb L e (u.val+1) K):∃ q: M→ Terra G τ d u→L[ℝ] E,Wealth q Y 1 ∧ Docked X hb (fun i=> L i-beneath (K:=K) (e:=e) X hb u q i) e u.val K := by
        let T:= bed G (d+u.val) (τ u); let Z(i:M):= Fallix G h K (X i) hb; let R': T→L[ℝ] Tracts G d τ:=ContinuousLinearMap.single (R:=ℝ) (fun x:Phase=> bed G (d+x.val) (τ x)) u
        let f(i:M):T→L[ℝ] E:= (L i) ∘L ((Z i).toContinuousLinearMap ∘L R'); have hT: Wealth f Y 1:= PledgeW hp (PledgeW (FallWeather h X hb Y hz).1 (wealthC _)); obtain ⟨q,hq,hQ⟩:= uplift T f hT hz
        let d':=upCap u e
        refine ⟨q,hq,fun i p hv=>?_,fun i p he=>?_⟩
        · change L i p-(q i) (StageM X hb u i p (e:=e) (K:=K))=0; rw[hx.hush i p hv,waysL,CapStone _ (hv u),map_zero,sub_zero]
        let v:=X i; let B:= atlasF G v hb K.K
        have hh:1≤τ u:= (show (1:ℕ)≤45 by decide).trans (awareLeaf h u); let U:bed G (d+u.val) (τ u):=⟨p.val u,oak p.val p.property u he⟩
        let b:T:= lava G _ _ hh K.K v hb (1/2) U; let A:= crestL G h u U; have hs: L i p=L i A:=sub_eq_zero.mp (by
                    rw[←map_sub]; apply hx.boom; intro y hy; change p.val y-A.val y=0; apply sub_eq_zero.mpr; by_cases hi:y=u; subst y; exact (crestP G h u U).1.symm; have ht:y.val<u.val:=(by have hx:y.val≠u.val:=Fin.val_injective.ne hi;omega); rw [he _ ht, show A.val y= _ from (crestP G h u U).2 _ ht])
        have hr:Z i (R' b)=A:=by rw[show Z i (R' b)= _ from landsZ h hb u b v hh]; apply congr_arg; apply Subtype.ext; erw [lavish,show b.val=_ from lavish hb u v U hh _]; simpa only [neg_neg] using! (sustain (-(1/2:ℝ)) B (τ u) (d+u.val) U.val) -- The two boosts have opposite parameters.
        change L i p-q i (StageM X hb u i p (e:=e) (K:=K))=0; apply sub_eq_zero.mpr; rw[hs,← hr]; let x:= Ov G d' (d+u.val) (τ u) b; rw [show StageM (K:=K) (e:=e) X hb u i p=x.val from ?_,hQ i x]; swap
        · rw [waysL]; change Cap _ _ _ _ _= Cap _ _ _ _ b.val; rw[show b.val=_ from lavish hb u v U hh _]
        apply sub_eq_zero.mp; change f i b-f i x=0; rw[←map_sub]; apply hx.hush i (Z i (R' (b-x))); refine OrbitS (X i) hb h (R' (b-x)) ?_
        intro l; by_cases hd:l=u; subst l; rw [show R' (b-x) u=b-x from (by simp[R'])]; exact CapLate b.val (m:=τ u) d'; rw [show R' (b-x) l=0 from (by simp [R',hd])]; exact Phere.hush _
end
end hum
end YM.OPE.Stroke
