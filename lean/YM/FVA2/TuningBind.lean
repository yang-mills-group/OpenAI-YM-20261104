import YM.FVA2.Visual
/-!
# Linear operations on marks of k-frame

Transport canonical generators with full space coercion alongside the real fields.
Note equivariance of the **LPT** Taylor proof across changes is used after run only
where available; no translating orbit estimate across different lattices.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 750000
set_option quotPrecheck false
namespace YM.FVA2.Blaze
open Lattice MS MS.Local.Physical MS.Menus MS.SpinCode MS.Plane MS.City MS.Wind.Leading
open ColorCode Warehouse Plate Filter Topology Set Function MeasureTheory PertExtension
open Wilson MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio MS.Native.Paint
open MS.Native.Orient MS.Native.Sew MS.Native.Draft MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Program
open MS.Cylinder MS.Cylinder.Lab MS.Cylinder.Taylor MS.Book.Convolve MS.Tone MS.Color MS.Plane.Flux
open MS.Logarithm MS.High MS.High.Knobs MS.Wind
open scoped Topology Classical ContDiff
variable {G:Gauge} (s:Signed){D:Deck G}(TQ: Warehouse G)
section power
variable {I:Type}(P:Finset I) (q:I→Power G) (c:I→ℝ)
-- use value formula Avg and Pose
def fusionP : Power G where
   allowance:= P.sup fun i=> (q i).allowance
   input:= ∑ i∈P,(c i:ℂ) • (q i).input
   polyn:= by
       rw [show ∑ i∈P,(c i:ℂ) • (q i).input= (fun x:ℝ=>∑ i∈P,(c i:ℂ) • (q i).input x) from funext fun x=> Finset.sum_apply ..]; exact value_sum _ fun i _=> Ready.scale (q i).polyn (c i) -- ℝ-Or scalar order
   actual x:= by rw [Finset.sum_apply]; exact Tune.sum _ fun i _=> ((q i).actual x).cash _ (by simp)
   calm x:= by rw [Finset.sum_apply]; exact Colorless.csum _ fun i _=> ((q i).calm x).smul _
   ranks x:= by rw [Finset.sum_apply,sum_stack]; exact Limit.sum _ fun i hi=> by have h:(q i).allowance ≤ P.sup fun i=> (q i).allowance:= Finset.le_sup (f:=fun i=>(q i).allowance) hi; exact ((q i).ranks x).up (by omega) |>.smul (c i:ℂ)

def shifted (p:Power G): Power G where
   allowance := p.allowance
   input := fun x=> Native.Orient.pose s (p.input x)
   polyn := p.polyn.linear ((Native.Orient.pose s).restrictScalars ℝ)
   actual x:= shaded s (p.actual x)
   calm x:= tinting s (p.calm x)
   ranks x:= ceiling s (p.ranks x)
end power
section cost
local notation "B"=> wings G
variable {I:Type}{d:ℕ} (P:Finset I)(q:I→ Acts D d)(c:I→ℝ)
def fuse : Acts D d:= fun i=> ⟨ ∑ j∈P,c j • (q j i).register, fusionP P (fun j=> (q j i).proof) c ⟩
lemma register_fuse (i k): (fuse P q c k).register i=∑ j∈P,c j • (q j k).register i:= Finset.sum_apply ..
lemma low_fuse (e:ℤ)(h:∀ i∈P,∀ x, Limit ((q i 0).proof.input x).val e)(x:ℝ): Limit ((fuse P q c 0).proof.input x).val e:= by
    change Limit ((∑ i∈P,(c i:ℂ) • (q i 0).proof.input) x).val e; rw [Finset.sum_apply,sum_stack]; exact Limit.sum _ fun i hi=> (h i hi x).smul (c i:ℂ)
variable (V: BookM D) (p:Team)
lemma oil_f (i k x) : Menus.oil (fuse P q c) i k x=∑ j∈ P,(↑(c j):ℂ)*oil (q j) i k x:= by
    unfold Menus.oil; rw [register_fuse,Polynomial.eval_finsetSum]; simp only [Polynomial.eval_smul,Complex.ofReal_sum, smul_eq_mul, Complex.ofReal_mul]
lemma rent_f : rentM V p (fuse P q c)=∑ i∈P,(c i:ℂ) • rentM V p (q i):= by
    funext x k; simp only [Finset.sum_apply, rentM,Pi.smul_apply,oil_f,Finset.sum_smul,mul_smul, Finset.smul_sum]; rw [ Finset.sum_comm (γ:=I) ]; -- swap triple
    exact Finset.sum_congr rfl fun p _=> Finset.sum_comm
lemma motto_f (x:ℝ) : motto p (fuse P q c) x= ∑ i∈P,(c i:ℂ) • motto p (q i) x:= by
   let T : LinearMap (RingHom.id ℂ) (T (Glow G)) (T (Glow G)):= ( Book.actB (Spectrum G) + Book.blocks (Spectrum G) (style G p x)); change T (prim (fuse P q c) x)= _;
   rw [show prim (fuse P q c) x=∑ i∈P,(c i:ℂ) • prim (q i) x from funext fun k=>by unfold prim fuse fusionP; simp only [Finset.sum_apply,Pi.smul_apply] ]; simp_rw [map_sum,map_smul]; rfl
lemma score_f : scoreM V p (fuse P q c)=∑ i∈P,(c i:ℂ) • scoreM V p (q i):= by
    funext x; simp only [scoreM,rent_f,motto_f,Pi.smul_apply,Finset.sum_apply,smul_add, Finset.sum_add_distrib]
lemma horizon_f : horizonM V p (fuse P q c)=∑ i∈P,(c i:ℂ) • horizonM V p (q i):= by
    refine Tick.unique (ticksM p _ _ 0 (aquaM V p (fuse P q c))) ?_; convert Tick.total P (U:=fun i=>(c i:ℂ) • horizonM V p (q i)) (f:=fun i=>(c i:ℂ) • (fun n x=>run (scoreM V p (q i) x n))) (fun i hi=>(ticksM p _ _ _ (aquaM V p (q i))).weight (c i)) using 1; funext n x; rw [score_f]; simp only [ Finset.sum_apply,map_sum,Pi.smul_apply,map_smul]

variable (γ:Acts (wings G) d)
def castA (s:Signed) : Acts (wings G) d:= fun i=>
   { register := fun j=> ∑ k:BasisIx G d, shows TQ.F s.ortho d k j • (γ i).register k, proof := shifted s (γ i).proof }
lemma oil_cast (i k x) : Menus.oil (castA TQ γ s) i k x=∑ j:BasisIx G d,(↑(shows TQ.F s.ortho d j i):ℂ) * oil γ j k x:= by unfold Menus.oil castA; simp only [Polynomial.eval_finsetSum,Polynomial.eval_smul,Complex.ofReal_sum, smul_eq_mul, Complex.ofReal_mul]
lemma rent_cast (x:ℝ) : rentM (TQ.native B) p (castA TQ γ s) x= Warehouse.markPose s ( rentM (TQ.native B) p γ x ):= by
    funext k; unfold Warehouse.markPose; rw [promised]; unfold rentM; rw [ map_sum ]; simp_rw [map_sum,map_smul, show ∀ j :ℕ,∀ u:BasisIx G d,pose s ( Glyph.preambleM (TQ.native B) p u x j )= _ from fun j u=> congr_fun (purpose d TQ p s x u) j ]; simp only [ Finset.sum_apply,Pi.smul_apply,Finset.smul_sum]; simp_rw [oil_cast,Finset.sum_smul,mul_smul,smul_comm (oil γ _ _ x) (↑(shows _ _ _ _ _):ℂ)];
    -- all Γ sums over k; commute
    let L := Finset.HasAntidiagonal.antidiagonal k; let f (i j:BasisIx G d)(a:ℕ×ℕ):= (shows TQ.F s.ortho d i j:ℂ) • oil γ i a.1 x • Glyph.preambleM ( TQ.native B ) p j x a.2
    change ∑ j:BasisIx G d,∑ a∈L,∑ i:BasisIx G d,f i j a=∑ i:BasisIx G d,∑ a∈L,∑ j:BasisIx G d,f i j a; rw [ Finset.sum_comm, Finset.sum_comm (f:=fun i a=> ∑ j:BasisIx G d,f i j a) ]; exact Finset.sum_congr rfl (fun i hi=> Finset.sum_comm)
lemma cost_cast (x:ℝ)(i:ℕ) : run (motto p (castA TQ γ s) x i)= rotD s (run ( motto p γ x i )):= by
    let K:= Spectrum G; simp only [sky,map_add,map_sum,rotD]; apply congr_arg₂ (·+·); · have hv := (γ i).proof.actual x; change run ((Spectrum G).Lap (pose s _))= _; rw [ lapC _ (shaded s hv).symm, lapC _ hv.symm, startL,rotD, mist_cc s⁻¹ (K_zone ..) ];
    apply Finset.sum_congr rfl; intro j _; change run ((Spectrum G).touch _ (pose s _))= _;  rw [funext ( touching (style G p x j.1) (pose s (( γ j.2).proof.input x)) ),funext (touching ( style G p x j.1) _),startL]; exact shadow_tree s⁻¹ (K_zone ..) (choral _ ((core_circle G p).stance0 _ _ rfl)) -- Cart
lemma score_cast (x:ℝ)(i:ℕ) : run (scoreM (TQ.native B) p (castA TQ γ s) x i)= rotD s (run (scoreM (TQ.native B) p γ x i)):= by simp only [scoreM,Pi.add_apply,map_add,rent_cast, cost_cast]; rw [ Warehouse.markPose,promised,startL]
lemma step_cast : horizonM (TQ.native B) p (castA TQ γ s)= Tick.shiftS s ( horizonM (TQ.native B) p γ ):= by refine Tick.unique (ticksM p _ _ 0 (aquaM (TQ.native B) p (castA TQ γ s))) ?_; simp_rw [score_cast]; exact Tick.shifted s (ticksM p _ _ _ (aquaM _ _ _)) -- metavariable
end cost
end YM.FVA2.Blaze
