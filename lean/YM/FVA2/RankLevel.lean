import YM.FVA2.VolumesH
import YM.FVA2.Generator
/-!
# Synthesize exactly the position-space jet readout

Argument about free propagator plus Taylor vertices; this is the last
input before testing Wick contraction on the compressed coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.PairCoords
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Chart
open Function Filter Metric MeasureTheory TreeBasis Trans
open Wilson Based GaussianScore MS.Orbit MS MS.Orbit.Cog MS.Swirl Green MS.Bare MS.Plane MS.Landau MS.Koszul
open Modes MS.Native MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Native.Draft MS.Native.Wilsonian MS.Native.Chart MS.Puff MS.Puff.Engine MS.Puff.Mom MS.Book MS.Book.Program MS.Bare.Focus Precision Finset
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {U J:Type} {n:Side} {Z: ChartRatio G} (hp:LocalRatio Z)
variable (m:Module.Basis U ℝ (Wilson.Field G n))(b:Module.Basis J ℝ (Param G n)) [Fintype U][Fintype J]
variable (he:_root_.Even n.val)

set_option quotPrecheck false
local notation "ιc" => ink (bell (J:=J) m)
local infixr:70 " ⬘ " => product (φ (U:=U) (J:=J))
local notation "Fκ" => Wilson.Field G n
local notation "Zκ" => plan G n
local notation "Φ" => plug (mkPlug m b)

abbrev block (U:Type) {J:Type} (j i:J) : BL (Slot U J):= product φ (atLetter (c i)) ( atLetter (bar j))
omit [Fintype U] [Fintype J] in
lemma swapped (j i:J) : (atLetter (bar j)) ⬘ atLetter (c i) = - block U j i:=
    Eq.trans (Pure.times_comm (p:=φ (U:=U) (J:=J)) (F:= atLetter (bar j)) (H:=atLetter (c i)) (speaks_p _) (speaks_p _)) (neg_one_smul ℂ (block U j i))

include he
lemma plug_ropes : Φ (pay true • (sumHome (ropes G (drive n) 0)).val) =
     ∑ j:J,∑ i:J, block U j i ⬘ ιc (bill b j i):= by
   let c0:ℝ:= (-1)/2; let P:= pay true
   have he0 (j i:J) : ιc (bill b j i)=∑ k:(Edge (Site n))×G.ColorIndex, ((c0*(kField b j k.1 k.2:ℝ):ℝ):ℂ) • ιc (vert b k.1 k.2 i) := by
         let v(k:Edge (Site n) × G.ColorIndex):=vert b k.1 k.2 i; let l (k:(Edge (Site n))×G.ColorIndex) := c0*kField b j k.1 k.2; have hv: bill b j i=ᶠ[𝓝 0] (∑ k,l k • v k):= by
             apply (bill_near b he j i).mono; intro x h; rw [h]; rw [Finset.sum_apply,Fintype.sum_prod_type]; simp_rw [neg_div,Finset.sum_div,← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro w _; exact Finset.sum_congr rfl fun i _=> by unfold l c0 v; rw [Pi.smul_apply,smul_eq_mul]; ring
         rw [ Taylor.inkit _ hv, ink_sum (F:=fun k=>l k • v k) _ _ (fun k _=> (cleanV ..).const_smul (l k))];
         unfold v l; simp_rw [ink_smul _ (cleanV (n:=n) b _ _ _)] -- Binder
   rw [map_smul,ropes_only]; rw [show (∑ e:Edge (Site n),∑ a:G.ColorIndex, (Φ (AHplus a e).val) ⬘ (Φ (throat (drive n) e a).val) )=∑ k:(Edge (Site n) × G.ColorIndex), (Φ (AHplus k.2 k.1).val) ⬘ (Φ (throat (drive n) k.1 k.2).val) from (by conv_rhs => rw [Fintype.sum_prod_type]) ];
   simp_rw [kPlug, to_steer,he0, _root_.map_sum, LinearMap.sum_apply, Finset.smul_sum]; rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
   apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun k _=>?_ ; rw [map_smul (product φ),LinearMap.smul_apply, map_smul,← times_assoc, swapped i j, map_neg,LinearMap.neg_apply,smul_neg,smul_neg]; rw [smul_smul];
   have hv (x:ℝ): ↑(c0*x) = -(pay true)*(x:ℂ) := by unfold c0 pay; push_cast; norm_num
   rw [hv,neg_mul,neg_smul]

lemma plug_action : Φ (pay true • (docket n (W G)))= - ιc (WilsonPull (plan G n)) + ∑ j:J,∑ i:J, block U j i ⬘ ιc (bill b j i):= by
   change Φ (pay true • (sumHome (shown n (W G))).val)=_; unfold W; rw [Orient.vessel,bosons,_root_.map_add, add_stack,smul_add,_root_.map_add,plug_weight,plug_ropes _ _ he]
omit he
section rank
variable {A:Type} (p:Sector A)
lemma previous (v:ℤ) (B: BL A) (h:rank v B): From B v:= fun i H=> h i (by rw [mod_int];omega)
lemma pickedRank (B Q:BL A) (k h:ℤ) (n:ℕ) (hb:Book.rank k B)(hc:From Q h): rankLevel (k+h) (product p B Q) n=product p B (rankLevel h Q n):= by
   rw [← pairLevel n (previous _ _ hb) hc, Finset.sum_eq_single (0,n),rankLevel]; rotate_left 2
   · simp
   · push_cast; rw [zero_add,show mask k B=B from (rank_hat k).mp hb]
   intro j hj h; unfold rankLevel; rw [rank_off hb ?_,map_zero]; rfl
   obtain he:=mem_antidiagonal.mp hj; intro he'; exact h (Prod.ext (by omega) (by simp only; omega))

lemma letter_level (i:A): Book.rank 1 (atLetter (R:=ℂ) i):= by intro w h; rw [Book.mod_int] at h; rcases w with _|⟨a,_|b⟩; rfl; simp at h; rfl
end rank

omit [Fintype U] [Fintype J] in
lemma rankPair (j i:J) : Book.rank 2 (block U j i):= Rails.product (letter_level (c i)) (letter_level (bar j))

-- interaction relative weight jets before coupling substitutions.
def Qpair (n : ℕ) : BL (Slot U J) := ∑ j:J,∑ i:J,block U j i ⬘ mask n (ιc (bill b j i))
def Qboth (k : ℕ) : BL (Slot U J) := Qpair m b k - mask (k+2) (ιc (WilsonPull Zκ)) + mask k (ιc (Real.log ∘ haar G n Z)) -- include coupling power only Q>=1

include he hp
lemma charged (k:ℕ): Φ (pay true • (docket n (core G k))) = Qboth (Z:=Z) m b k:= by
   change Φ (pay true • (docket n (levels 2 (W G) k + levels 0 (Wilsonian.H G) k)))= _
   have ht (w:ℤ) (F:Dot G _root_.YM.Lattice.Cover) : docket n (levels w F k) = mask (k+w) (docket n F):= enterShim (b:=true) n _ -- signature
   rw [map_add,smul_add, map_add, ht,ht]; simp only [← map_smul (mask _),cap_stem,plug_action m b he, plug_haar m b he Z hp, map_add,map_neg,map_sum]; unfold Qboth Qpair
   rw [sub_eq_add_neg,add_comm _ (-(mask (k+2) _)),add_zero]
   congr 2; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_; convert! (pickedRank φ _ (ιc (bill b i j)) _ 0 k (rankPair i j) (fun x hx=> by omega)) using 1
end YM.FVA2.PairCoords
