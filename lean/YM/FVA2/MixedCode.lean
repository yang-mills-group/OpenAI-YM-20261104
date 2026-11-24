import YM.FVA2.MixedStamps
import YM.MS.Menus.Tape
import YM.MS.Menus.Mark
import YM.MS.Menus.Quantify
import YM.MS.Wind.Clone
import YM.MS.Wind.Portfolio
/-!
# Menus-coded source steps, extended to allow multi-rank bare `BookM`

These portions of `Tide` and `High` (see above imports from which individual
 wrappers and proofs are adapted/rebound) can't be applied as-is to exact
 calibration with lower raw-rank terms. This file only rebinds the Menus-dependent
 lemmas to the already present stronger formulation; no change to MS-data,
 adjusted score/physical ending prescriptions (except their binding to `BookM`),
 proofs of the momentum estimates, or geometric predicates. Keep analogous names with
 suffix M. `Uses`, `Rake.Geo`, etc. the same.
-/
set_option autoImplicit false
noncomputable section
-- adapted from Menus/Tape
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G} (V : BookM B)(p:Team) {d:ℕ}
variable (A:Acts B d)
def rentM (x:ℝ) (i:ℕ): Dot G Cover:= ∑ g:Glyph B d, ∑ d∈antidiagonal i, oil A g d.1 x • Glyph.preambleM V p g x d.2
def scoreM (x:ℝ): T (Dot G Cover):= rentM V p A x + motto p A x
lemma steadyM (k:ℕ) (P:Acts B d) (H:∀ i, i≤ k→ A i=P i) (x:ℝ): scoreM V p A x k=scoreM V p P x k := by
    simp_rw [scoreM,Pi.add_apply,sky,rentM, H k k.le_refl]
    apply congr_arg₂ (·+·)
    · apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j hj; unfold oil; rw [H j.1 (by obtain h:=mem_antidiagonal.mp hj; omega)]
    congr 1; apply Finset.sum_congr rfl; intro j hj; rw [H j.2 (by obtain h:=mem_antidiagonal.mp hj; omega)]
lemma posesM (x:ℝ)(i:ℕ): Tuned (rentM V p A x i) 0:= Tune.sum _ fun g _=> Tune.sum _ fun j _=> (Glyph.pre_cM V p g x j.2).cash _ (show star (oil A g j.1 x)=_ from by simp [oil])
lemma appearsM (x:ℝ)(i:ℕ): Colorless (rentM V p A x i):= Colorless.csum _ fun g _=> Colorless.csum _ fun j _=> (Glyph.pre_litM V p g x j.2).smul _
lemma rentReadyM (i:ℕ): Ready (fun x=> rentM V p A x i):= value_sum _ (fun j _=> value_sum _ (fun k _=> pc_ready (c:=oil A j k.1) ⟨_,Ready.got _,rfl⟩ (Glyph.pre_readyM V p j k.2)))
lemma rentLimitM (x:ℝ)(i:ℕ): Limit (rentM V p A x i).val (i+d):= by unfold rentM; simp_rw [sum_stack]; exact Limit.sum _ (fun g _=> Limit.sum _ (fun k hk=> ((Glyph.pre_costM V p g x k.2).smul _).up (by obtain he:= Finset.mem_antidiagonal.mp hk; have hv:= Glyph.memory g; omega)))

lemma rangeM (x:ℝ)(i:ℕ): Limit (scoreM V p A x i).val (i+d+fringe A i):= Limit.add ((rentLimitM V p A x i).up (by omega)) ((stuff p A x i).up (by omega))
lemma decorM : Circle G (scoreM V p A) false 0 where
    stance0 _ _ h:= False.elim (Bool.noConfusion h)
    actual i x:= (posesM V p A x i).add (pretty p A x i)
    settled i x:=(appearsM V p A x i).add (colorRoot p A x i)
    tag i:= (rentReadyM V p A i).add (flows p A i)
    room i:=⟨i+d+fringe A i,fun x=>by exact_mod_cast (rangeM V p A x i)⟩
end YM.MS.Menus

-- adapted from Menus/Mark
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G}(V : BookM B)(p:Team) {d n:ℕ} (x:ℝ)
section close
variable (A:Acts B d)(H:G.Simple)
include H
lemma rentedM : Weightless (Spectrum G) (style G p x) (rentM V p A x):= by
    let P:=Spectrum G; let T:Glyph B d→ T (Dot G Cover):= fun i=> Glyph.preambleM V p i x;
    let U (ζ:Glyph B d)(n:ℕ) := oil A ζ n x; let X := style G p x; let D:=actB (Spectrum G)+ pairW (Spectrum G).touch X; let J:= pairW (LinearMap.lsmul ℂ (Dot G Cover));
    have he c f: actB P (J c f)=J c (actB P f):= by funext n; unfold actB J; simp only [paired,promised, LinearMap.lsmul_apply,map_sum,map_smul]
    have hd (i:Glyph B d): D (J (U i) (T i)) =0:= by rw [show D (J (U i) (T i))=J (U i) (D (T i)) from ?_,show D (T i)=0 from Glyph.pre_freeM V p i x H,map_zero]; unfold D; simp only [LinearMap.add_apply, olio, J,map_add]; rw [show actB (Spectrum G) _ =_ from he (U i) (T i)] -- lint
    change D _=0; rw [show rentM V p A x=∑ g:Glyph B d,J (U g) (T g) from funext fun n=> by unfold rentM; simp only [Finset.sum_apply]; rfl,map_sum]; simp_rw [hd,Finset.sum_const_zero]
lemma lawM : Weightless (Spectrum G) (style G p x) (scoreM V p A x):= by
    let Q := actB (Spectrum G)+ blocks (Spectrum G) (style G p x); change Q (rentM V p A x+motto p A x)=0
    have hh : Q (motto p A x)=0 := steady_squares (style G p x) _ (main_law G p x H) (fun i=> ((core_circle G p).actual i x).symm) (fun i=> Tune.parity ((core_circle G p).actual i x) ghostParity) (fun i=> ((A i).proof.actual x).symm)
    rw [map_add,hh,show Q (rentM V p A x)=0 from rentedM V p x A H,zero_add]
end close
def lightingM (Q: Price B d) (x:ℝ): Dot G Cover:= ∑ c:Glyph B d, (↑((Q c).eval x):ℂ) • Glyph.preambleM V p c x 0
variable (A:Acts B d)(Q:Price B d)(X:Power G)
lemma repairM : scoreM V p A x n-scoreM V p (patch A Q X n) x n= lightingM V p Q x + advance (X.input x):= by
   let S:= patch A Q X n; have hc : (A n).proof.input x-(S n).proof.input x = X.input x:= by simp [S,patch,Power.sub] -- may `sub_sub`
   have hs (i:Glyph B d) : ∑ j∈antidiagonal n,(oil A i j.1 x - oil S i j.1 x) • Glyph.preambleM V p i x j.2= (↑((Q i).eval x):ℂ) • Glyph.preambleM V p i x 0:= by
        rw [Finset.sum_eq_single (n,0)]; simp [oil,S,patch] -- check
        · intro j hj hne; by_cases h : j.1=n; · obtain ht:=mem_antidiagonal.mp hj; exact (hne (Prod.ext h (by dsimp; omega))).elim
          simp_rw [oil, show S j.1= A j.1 from patch_bef A Q X h,sub_self,zero_smul]
        simp
   rw [scoreM,scoreM,Pi.add_apply,Pi.add_apply, add_sub_add_comm,lightingM]; congr 1
   · unfold rentM; simp_rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro c _; rw [← hs c]; exact Finset.sum_congr rfl (fun k _=> (sub_smul (oil A c k.1 x) (oil S c k.1 x) (Glyph.preambleM V p c x k.2)).symm)
   rw [sky, sky, add_sub_add_comm, ← map_sub,hc,advance]; congr 1
   rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (0,n)]; dsimp only; rw [← map_sub,hc, style,whoZero]; -- check
   · intro j hj hne; obtain h :=mem_antidiagonal.mp hj; have h' : j.2≠n:= fun g=> hne (Prod.ext (by dsimp; omega) g); rw [patch_bef _ _ _ h', sub_self]
   simp
end YM.MS.Menus

-- adapted from Menus/Quantify
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost Detect
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G}(V : BookM B)(p:Team) {d n r:ℕ}{v:ℤ}
namespace Glyph
variable {P S:ℝ→ Law G} {Q:Price B d}
lemma hitsM (h: Homes Q v r)(x:ℝ) : Limit (lightingM V p Q x).val r ∧ Fits (lightingM V p Q x) (valAt Q x) r v false:= by
    refine ⟨?_,Fits.sum _ (fun i _=>?_)⟩; swap
    · by_cases he: Q i=0; · simp only [he,Polynomial.eval_zero,Complex.ofReal_zero]; rw [zero_smul,zero_smul]; exact Fits.zero _
      rw [← h.size i he, ← h.grade i he]; exact (Glyph.pre_floorM V p i x).smul _
    unfold lightingM; rw [sum_stack]; refine Limit.sum _ fun c _=>?_ ; by_cases he: Q c=0; rw [he,Polynomial.eval_zero,Complex.ofReal_zero,zero_smul]; exact fun _ _=> rfl; rw [← h.grade c he]; exact Limit.smul _ ((by simpa using pre_costM V p c x 0) : Limit (preambleM V p c x 0).val c.grade)
-- offer polynomial class. choose in homogeneous dimension slice only
end Glyph
structure CapacityM (A C:Acts B d)(n r:ℕ)(v:ℤ) (H:ℝ→ Law G): Prop where
    past (i:ℕ): i<n→ A i=C i
    size (x:ℝ): Limit ((scoreM V p A x n)-(scoreM V p C x n)).val r
    jet (x:ℝ): Fits ((scoreM V p A x n)-(scoreM V p C x n)) (H x) r v false
-- permits leading reservation: if at order0 and r below highest rank the parameters are special. Later.
lemma room_hereM (A:Acts B d) {P H:ℝ→ Law G}(h:0≤v)(ht:v≤d)(hp:Ready P)(hq:Ready H) (hc : ∀ i,P i∈B.carries v r)(hd:∀ i,H i∈ Lease G (v-1) r (-1)): ∃ (Q:Price B d) (X:Power G), Glyph.Homes Q v r ∧ X.allowance=r ∧ CapacityM V p A (patch A Q X n) n r v (fun i=> P i+natQ (H i)):= by
    obtain ⟨Q,hQ,hF⟩:= Glyph.offered h ht hc hp; obtain ⟨X,hx,hX⟩:= pens hq hd; have he (x:ℝ): Limit (advance (X.input x)).val r∧ Fits (advance (X.input x)) (natQ (H x)) r v false:= estimateL x (hx ▸ X.ranks x) (hX x)
    refine ⟨Q,X,hQ,hx,⟨fun i h=> (patch_bef A Q X h.ne).symm, fun x=>?_, fun x=>?_⟩⟩ <;> rw [repairM]; exact (Glyph.hitsM V p hQ x).1.add (he x).1; rw [← hF x]; exact (Glyph.hitsM V p hQ x).2.add (he x).2
end YM.MS.Menus

-- adapted from Wind/Clone
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{p q:Team}{φ φ':Actor G}{F H V: Dec G}{b:Bool}{k r d:ℕ}{l:List (Lane4 G)}{u:ℤ}
variable {B: Local.Physical.Deck G} (W:BookM B)
-- mark with canonical action; uses all t, 'A arbitrary finite dimensions.'
def horizonM (W:BookM B)(p:Team)(A:Acts B d): Dec G:= (member (skyPC G p) (decorM W p A)).choose
lemma aquaM (W: BookM B)(p:Team)(A:Acts B d): PM (scoreM W p A) (skyline G p) (horizonM W p A) 0 := (member (skyPC G p) (decorM W p A)).choose_spec
lemma money_beforeM (A C:Acts B d)(h:∀ i<k,A i=C i) : ∀ i<k,horizonM W p A i=horizonM W p C i:= mark_birth (aquaM W p A) (aquaM W p C) (fun j hj x=> steadyM W p A j C (fun i hi=>h i (by omega)) x) -- order of steadyM args?
lemma mark_payM {Z:ℝ→ Law G}{A C:Acts B d}(hf:CapacityM W p A C k r u Z): Knick (horizonM W p A k) (horizonM W p C k) r u false Z:= by
    let T:= horizonM (d:=d) W p; let F':=skyline G p; have he: path 1 k 0 F' (T A)=path 1 k 0 F' (T C):= path_eq _ _ _ (fun _ _=>rfl) (fun i hv=> money_beforeM W A C hf.past _ (path_in hv).2)
    refine knick ((aquaM W p A).owes k) ((aquaM W p C).owes k) ((aquaM W p A).recu k) (fun x=>?_) hf.jet hf.size; rw [he]; exact (aquaM W p C).recu k x
end YM.MS.Wind

-- adapted from Wind/Portfolio
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting Knobs Local.Physical
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge} {U:ℕ→Type}{p q:Team}{φ φ':Actor G}{F H V: Dec G}{b:Bool}{k r d:ℕ}{l:List (Lane4 G)}{u:ℤ}
variable {B:Deck G}(W: BookM B)
def SeekM (W: BookM B)(p:Team)(d:ℕ): Knobs (fun _=> Tact B d) G where
   wake A:= col (horizonM W p A)
   stay A C i h:= by funext y; unfold col; rw [money_beforeM W A C (k:=i+1) (fun j hj=>h j (by omega)) _ (by omega)]
lemma mark_seekM (h: G.Simple): Marked (SeekM W p d) (col (skyline G p)) B d where
    law A:= PMSolve h (skyPC G p) (aquaM W p A) (decorM W p A) (fun x=> lawM W p x A h)
    occurs A:= post_ok _ (aquaM W p A).owes
    moves A i r v hv ht a b hp hq hk hK:= by
       obtain ⟨Q,X,H1,H2,H⟩:= room_hereM (n:=i) W p A hv ht hp hq hk hK; exact ⟨_,rewind (K:=SeekM W p d) (hp:=A) (hq:=Menus.patch A Q X i) rfl rfl H.past (fun x=>(((aquaM W p A).owes i).stay x).joint) (fun x=> (((aquaM W p _).owes i).stay x).joint) (mark_payM W H)⟩
end YM.MS.Wind
