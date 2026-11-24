import YM.FVA2.Command
import YM.X.Stage.T1
import YM.X.Bare.Marks
/-!
# Same literal matrix horizon and bare coefficients as the perturbative position prescription

Give its moment bank also pointwise and with no position smearing. In finite lattice tests the
bare convention samples on positions x with one common center. This is PRIOR any coupling change.
Proof via Stamp issuance in factor tensor algebra Price. ξ.K standard.
-/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1100000
namespace YM.FVA2.BoxOffice
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Bare.Shop
open Wilson Lattice Gauge Labels PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open PertExtension.LatticePT RG FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.MultiGauge FormalOPE.RG10.InversionTop
open MS MS.Koszul MS.Theater MS.Book MS.Book.Program MS.Book.Convolve
open Clock Score Based PairCoords Modes Paper Trans
open PowerSeries Attend
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius

variable {G:Gauge} (V: Warehouse G) {U J : Type} {n m d:ℕ} {N:Side}
local notation "F"=>V.F
local notation "ψ"=> PairCoords.φ (U:=U) (J:=J)
abbrev warehouse (V:Warehouse G): PositionX.Bare.Shop V.F:= ⟨V.H,V.S,V.h,V.acts⟩
abbrev cast (W:LatticePT.Word G)(i:W.F.Index)(u:Site N): MultiGauge.Splice.Ticket (Wilson.Field G N):= Source.seated u ( W.F.grades i ).2 (Plate.bare W.S i)
def billV (e:ℝ)(w: LatticePT.Word G)(k:w.F.Index) : ℝ:= (e^w.d)⁻¹* topBasis w.S w.H w.sound w.chosen w.axis k
lemma W_cost (w:LatticePT.Word G)(e:ℝ)(j:w.F.Index): w.cost j e=e^4* billV e w j:= by rw [Word.cost,billV,div_eq_mul_inv,mul_assoc] -- ring
section banks
variable (b:Module.Basis U ℝ (Wilson.Field G N))(u: Site N)(e:ℝ)(d:ℕ)
local notation "ιψ"=> Boson.sharp (bell (J:=J) b) φ (bell_even b)
def enter (u:Site N)(e:ℝ)(w:LatticePT.Word G) : Price ψ:= ∑ i:w.F.Index,(↑(billV e w i):ℂ) • ιψ (cast w i u)
-- `Bare.common` across heights.
def gate : Label G d→ₗ[ℂ] Price ψ:= PositionX.Bare.common (warehouse V) (enter b u e) d
def velvet : E V.F d→ₗ[ℂ] Price ψ:= gate V b u e d ∘ₗ RawLabels.physicalLabel V.F d
abbrev raw (i: V.Atom d):= PositionX.Bare.useWord (warehouse V) i
lemma gate_name (i: V.Atom d): gate (J:=J) V b u e d ((V.scene d).basis i)= enter b u e (raw V d i):= PositionX.Bare.common_name ..
lemma gate_scale {s t:ℕ}(h:s≤t)(p:Label G s): gate (J:=J) V b u e t (raiseLabel G h p) = gate V b u e s p:= PositionX.Bare.common_scale ..
lemma velvet_scale (h:d≤n)(p:E V.F d) : velvet V (J:=J) b u e n (up F h p)=velvet V b u e d p:= by unfold velvet; rw [LinearMap.comp_apply,show RawLabels.physicalLabel _ _ (up F h p)= _ from RawLabels.physical_inclusion F (scheme_filters F) h p, gate_scale ]; rfl
end banks
section grid
variable [Fintype U][Fintype J][DecidableEq J] (he:Even N.val)(b:Module.Basis U ℝ (Wilson.Field G N))(g:Module.Basis J ℝ (Param G N))(e:ℝ) (v:Fin n→ Site N)
local notation "η"=> (Currency b he (J:=J))
local notation "ιψ"=> Boson.sharp (bell (J:=J) b) φ (bell_even b)
abbrev unmarked (b:Module.Basis U ℝ (Wilson.Field G N))(g:Module.Basis J ℝ (Param G N)) : Price (PairCoords.φ (U:=U) (J:=J)):= Score.total (Orb.tray G) b g
-- guide for ANY Wick realization basis. Calculation diagram supported F0. Show to cost representation for each component.
local notation "W"=> unmarked b g
local notation "Ξ"=> Attend.guide η W
omit [Fintype U] in
lemma hungry (p:Module.Basis U ℝ (Wilson.Field G N)) : track ψ ( unmarked p g ) 0=0:= by rw [tracking,total_min (Orb.tray G) (Orb.traySpec G) ]; rfl -- unfold
lemma enjoy (p: MultiGauge.Splice.Ticket (Wilson.Field G N)): Ξ (ιψ p)= into (Score.exchange he (Orb.tray G) p) := by apply reserve; rw [← Clock.out_real]; exact guides η W (hungry g b) _ (Score.at_end he (Orb.tray G) (Orb.traySpec G) b g p) -- arg order

def key (d:ℕ) : MultilinearMap ℂ (fun _ : Fin n=> Label G d) Cn:= (guide (Currency b (J:=J) he) (unmarked b g)).compMultilinearMap (( MultilinearMap.mkPiAlgebra ℂ (Fin n) (Price (PairCoords.φ (U:=U) (J:=J))) ).compLinearMap (fun i=> gate V b (v i) e d))
def view (d:ℕ) := (key V he b g e v d).compLinearMap (fun _ => RawLabels.physicalLabel F d)
lemma keyD (l: Fin n→ E V.F d): view V he b g e v d l=Ξ (∏ i, velvet V b (v i) e d (l i)):= rfl
lemma view_scale (h:d≤ m) : (view V he b g e v m).compLinearMap (fun _ => up F h)=view V he b g e v d := by ext l; rw [MultilinearMap.compLinearMap_apply,keyD,keyD]; simp_rw [velvet_scale]

variable (w:Fin n→ V.Atom d)
def members (w:Fin n→ V.Atom d): Fin n→ LatticePT.Word G:= fun i=> raw V d ( w i )
local notation "Πv"=>members V w
local notation "Β" => V.Atom d
section tickets
-- Avoid division from auxiliary.ZR=1.N root. Exact scalar Line equation for diagonal coeff
variable (t: Mixed.Task (members V w))
def realPrice : ℝ:= ∏ i:Fin n,billV e (Πv i) (t i)
abbrev clan i:=Track.Seals V v (fun i=> ((V.scene d).grades ( w i ) ).1) t i
omit [Fintype U] [Fintype J] [DecidableEq J] in
private lemma kernelS (Y:Fin n→ V.Atom d)(t: Mixed.Task (members V Y))(i:Fin n) : cast ((members V Y) i) (t i) (v i)= Track.singleStamp V (v i) (d:=((V.scene d).grades (Y i)).1) (t i):= rfl
include he
lemma latticePrice : Ξ (∏ i:Fin n, (billV e (Πv i) (t i):ℂ) • ιψ (cast (Πv i) (t i) (v i))) = (realPrice V e w t:ℂ) • into ( Channel.realRead (clan V v w t) Finset.univ ):= by
   rw [realPrice, ← MultilinearMap.mkPiAlgebra_apply (R:=ℂ), MultilinearMap.map_smul_univ (m:=fun i=>ιψ (cast (Πv i) (t i) (v i))), MultilinearMap.mkPiAlgebra_apply ]; rw [ ← map_prod, map_smul,enjoy,Complex.ofReal_prod]; exact congr_arg (fun k: PowerSeries ℝ=>(∏ i:Fin n,(billV e (Πv i) (t i):ℂ)) • into k) (Track.pays_rows V v (fun i=> (Πv i).d) (fun i=> t i) Finset.univ he).symm
omit [Fintype U] [Fintype J] [DecidableEq J] he in
lemma goods : Orb.LocalTest ( Orb.restrictedO ( Stamp.shafts (clan V v w t) Finset.univ )):= by
   let S:= clan V v w t; have he(s:Finset (Fin n)): Orb.LocalTest ( Orb.restrictedO ( Stamp.shafts S s )):= by
       induction s using Finset.induction_on with| empty=>rw [Stamp.shafts,Finset.prod_empty ]; exact Orb.one_test| insert a s h ih=>
           let L:= (V.scene d).grades (w a)|>.1; let C₁:= Orb.restrictedO ( Stamp.shafts S s ); let C₀ := Orb.restrictedO ( (S a).stencil );
           have hx: Orb.LocalTest C₀:= (Orb.SlotEvaluation.pre_field (V.S L) (V.h L) (V.acts L) (t a) (v a)).1.curved; rw [show Stamp.shafts S (Insert.insert a s)= (S a).stencil* Stamp.shafts S s from Finset.prod_insert h]; exact ⟨hx.boundedness.mul ih.boundedness,ContDiffAt.mul hx.germ ih.germ⟩
   exact he Finset.univ

omit [Fintype U] [Fintype J] [DecidableEq J] in
lemma dia_scalar {X:Orb.Observable G N}(hv:Orb.LocalTest X)(k:ℝ): Orb.diag (k • X)= k • Orb.diag X:= by
   have hp: Orb.LocalTest (k • X):= ⟨hv.boundedness.const_smul k, hv.germ.const_smul k⟩; have hm:= Orb.finite_formula he ( Orb.traySpec G ) hp; have ht:= Orb.finite_formula he ( Orb.traySpec G ) hv; apply Aspiration.unique hm; unfold Orb.diag; rw [ show Orb.expectation (k • X)= k • Orb.expectation X from ?_ ]; swap
   · ext1 p; unfold Orb.expectation Orb.numerator Orb.entries; rw [ Pi.div_apply, Pi.smul_apply,Pi.div_apply ]; simp_rw [ Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul,mul_div_assoc k ] -- integral variant
   intro n; obtain ⟨C,hC,h⟩:= ht n; refine ⟨‖k‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩; filter_upwards [h] with i hi; have ht(a:ℕ→ℝ): peval (k • a) n i=k * peval a n i:= by simp [peval,Zone.eval,Finset.mul_sum,mul_left_comm _ k]
   simp_rw [ Pi.sub_apply, ht, Pi.smul_apply,smul_eq_mul, ← mul_sub, norm_mul ]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)

omit [Fintype U] [Fintype J] [DecidableEq J] in
lemma deals (j:ℕ):
   (e^4)^n * realPrice V e w t * (PowerSeries.coeff j (Channel.realRead (clan V v w t) Finset.univ)) = Orb.diag ( Orb.restrictedO ( Mixed.product (members V w) Finset.univ t v e )) (Mixed.number (members V w) t+j):= by
   let r:ℝ:= (e^4)^n*realPrice V e w t; let N₁:= Stamp.shafts (clan V v w t) Finset.univ; rw [show Orb.restrictedO _=r • Orb.restrictedO N₁ from ?_, dia_scalar he ( goods V v w t) r ]; · rw [Channel.realRead, MultiGauge.Stack.drop,coeff_mk,coeff_mk ]; rfl
   have hu: Mixed.product (members V w) Finset.univ t v e = r • N₁:= by funext u; unfold Mixed.product; simp_rw [W_cost,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin ]; simp only [ N₁,Pi.smul_apply, Stamp.shafts, Finset.prod_apply ]; rfl
   rw [hu]; rfl
end tickets
end grid
end YM.FVA2.BoxOffice
