import YM.RG05Readout.Capture.Splurge
/-!
# Group mission on issued state. Rebate

Specialize all continuations and charge a dummy marker when cluster peg/root
needs one. The played polynomial sees all these powers, so can verify exact
cycle even on artificial orientations. Normalize markers BEFORE calls, no
volume-dependent Schwinger restrictions here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open Ribbons Ribbons.Fibers Ribbons.ManyCopies
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d b:ℕ}{V W:Type}[DecidableEq W][Fintype W][DecidableEq V][Fintype V]
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {k l g:ℕ}
set_option quotPrecheck false
local notation "S0"=> C.path.levels
local notation "K"=> C.path.levels.clock
local notation "Y"=> C.path.rep N p
local notation "X"=> C.path
local notation "Ζ"=> C.path.levels.budget
local notation "u"=> Legato.Bandage.renal C.path.levels
local notation "p0"=> C.path.levels.budget n
local notation "t"=> (Ζ n).supportExponent
variable (o:Unit×W→Site (C.side n p)) (E:Unit×W→Motion) (s:Unit×W→ℕ) (I: ∀ i:ℕ,ManyStem C o i→Body)
local notation "V'"=> ManyStem C o
local notation "A'"=> Mine.tree o E
local notation "Λ"=>(A').labelY
local notation "Φ"=>(A').narrows
local notation "H!"=> Mine.ward o E
local notation "r₀"=>(A').supportX
variable (h:C.Makes) (L:OPE.Package C w r D) (hw:Storage C D) (heC:Cater C D)
variable {B:ℕ→ℕ→ℝ}{Q:ℝ} {Λ':Census (Unit×W)} {F:∀ i:ℕ, Config G (C.side i p)→Poly (Mine.ward o E Λ' i)}

variable (P:(i:Unit×W)→ Sight C (s i) p) (S:(i:Unit×W)→Emblems C (s i)) (x:(i:Unit×W)→Palette C (s i)) (T:Ribbons.Fibers W V)
local notation "v"=> Launch (m:=m) s S x
local notation "T!"=> plants (m:=m) s P S x
local notation "λ₀"=> fun i : V' N=>stepUp ((A').motion (Λ N i)) (r₀ N i) (entrance C (s (Λ N i)) N p (v (Λ N i) N) 0 (I N i))
local notation "Z0"=> apron C.path.levels
local notation "Tw"=> (Ribbons.ManyCopies.partialGroup Unit T)
local notation "l!"=> Ribbons.peepers C.path.levels n

-- peepers rung pointwise. homogeneous uniform charge for fixed arity
noncomputable def syrup (C: Family G)(m n d k b:ℕ)(Q:ℝ) := Fibers.Salt.tow (fun _ : Unit=> crust C m n d k Q) ((C.path.levels.budget n).supportExponent+1/2) (Bandage.renal C.path.levels n/b) (peepers C.path.levels n) ()
noncomputable def fee (C: Family G)(m n d k b:ℕ)(Q:ℝ) := syrup C m n d k b Q ^ b
local notation "ζ"=> fee C m n d k b Q
local notation "σ"=> crust C m n d k Q
variable (U: Unit×W→ℂ)
include h hw L heC
variable {Z:Census (Unit×V)}
set_option maxHeartbeats 800000 in
lemma recompense (H:∀ i:Unit×W,Spine D B h n p (s i) N (P i) (S i)) (hn:0<n) (hk:n < m)(hm:m ≤ N)(ho:Occupancy o ((K).J n))
    (hc:Clearance o E s I Λ' m) (hp:PreparedA A' I n N le_rfl) (hQ:∀ j: V' n, Cap (s (Λ n j)+2) (I n j) 1)
    (hX:∀ i:Unit×W,size (x i) ≤ Q) (hy:0 < Q) (ht:Warm C n (d+1) k) (hS:∀ i:Unit×W,s i ≤ d)
    (hF:F N=birth (Mine.ward o E Λ' N) (Y N) λ₀)(hr:Replay A' s (H:=H! Λ') (le_refl n) N F N)(hh:∀ i, ‖U i‖ ≤ 1)(hf:0<b)(hb:∀ i:Unit× V,((Tw).contents i).card ≤ b)
    (s':Finset V)(ha:∀ i∈s', T.Solo i)(hT: Pantry.Policy T Λ' Z)(h_l:∀ i:Unit×W,coverNumber (Ζ n).B ({(o ∘ (Tw).twig) ((Tw).bunch i),o i}:Support (C.side n p)) ≤ l!) :
    let A i:= baseFold o E Λ' (F n i)
    let q:= fun i=> Pantry.pilot T hT (spice Λ' U A i)
    let qx := (imprint h A' I T! n (hk.le.trans hm)) ∘ (Mine.remap o E).symm
    0< ζ∧ ∃ X':Unit×V→Three G (C.side n p), MenuBoard (Y n) X' q (o ∘ (Tw).twig) (fun _=> ζ) (t-2) 1 ∧
        ∀ i:Unit×V, let x:=(Tw).twig i; (i.2∈s' → X' i= stuff (qx x) (Y n) (U x)) ∧ (i.2∉s' → MergeProof.Float.Blade (Y n) (o x) ((X' i).snd.1) (profile ((Y n).activities) ((X' i).snd.2)) 0 (4*(1/ζ))):=by
    intro A q p'; have hhX:= h.wilson.represents N p n (hk.le.trans hm); let a:= u n; let C₀:=Y n; let D':=(Tw)
    have hΨ : Arsenal C₀:=by
       cases n with
       | zero=> omega
       | succ n=> obtain ⟨z,y,hC,-⟩:= heC.tiers n N p (Nat.lt_of_succ_le (hk.le.trans hm)); exact hC.publishes.contact
    obtain ⟨hσ,hp',b',hZ,hA⟩:=panorama o E s I h L hw heC P S x H hk hm ho hc hp hQ hX hy ht hS hF hr
    have hs : C₀.p=Ζ n:=hhX.vac; obtain ⟨hg,hY,hV,hN,h,Hq,hS'⟩:=hZ.eye
    let N':= syrup C m n d k b Q; have he:0 < N':=by unfold N' syrup Fibers.Salt.tow; positivity
    have hb' : N'≤1:= by
       have hs':a/(b:ℝ) ≤ 1:=(div_le_self (show 0 ≤ a from hY.le) (show 1 ≤ (b:ℝ) from Nat.one_le_cast.mpr hf)).trans hV
       apply le_trans (div_le_self (show 0 ≤ a/(b:ℝ)*σ from by have h:0<a:=hY; positivity) (Real.one_le_exp (mul_nonneg (by change 0≤ t +1/2; linarith only [hN]) (Nat.cast_nonneg _)))) (mul_le_one₀ hs' hσ.le ((show σ ≤ 1/2 from min_le_left ..).trans (by norm_num))) -- arg err
    have hv (i:Unit×W): (σ)*‖U i‖ ≤ 1/2:= (mul_le_of_le_one_right hσ.le (hh _)).trans (min_le_left ..)
    let U₀:=fun i:Unit×W=>stuff (p' i) C₀ (U i); let f:= spice Λ' U A; have hB0 : Alcove C₀ U₀ f o (fun _=>σ) b' a 1:= (show (1:ℝ)/2+1/2=1 from by ring) ▸ hA.spiced U hv (fun _=>hσ.le)
    let r'(j:Unit×V):= ∏ _i∈ D'.contents j,N'; let S'(j:Unit×V):= ∏ i∈ D'.contents j,Fibers.Salt.tow (fun _=>σ) (C₀.p.supportExponent+1/2) (a/b) (l!) i
    have hg'(i): ζ ≤ S' i:=by
         change N'^b ≤ _; have hr: S' i= N'^(D'.contents i).card:=by unfold N' S' syrup; rw [hs]; exact Finset.prod_const _
         rw [hr]; exact pow_le_pow_of_le_one he.le hb' (hb i)
    have hoP: Occupancy o (Z0 n):= fun i=> (ho i).trans (((S0|>.fits.mono n.le_succ).trans (Nat.le_add_right ..)).trans (Nat.le_mul_of_pos_right _ (pow_pos (C.S.block n).property _)))
    have hXk: Occupancy (o ∘ D'.twig) (Z0 n):=by
       intro i; let B':=Finset.univ.filter (fun j:Unit×V=> o (D'.twig j)=i); let L:=Finset.univ.filter fun j:Unit×W=> o j=i
       apply le_trans (le_of_eq (Finset.card_image_of_injOn (s:=B') D'.sectioned.injective.injOn).symm) (le_trans (b:=L.card) _ _)
       · refine Finset.card_le_card ?_; intro j hj; obtain ⟨j,hJ,rfl⟩:=Finset.mem_image.mp hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hJ).2⟩
       exact (ho i).trans (((S0|>.fits.mono n.le_succ).trans (Nat.le_add_right ..)).trans (Nat.le_mul_of_pos_right _ (pow_pos (C.S.block n).property _)))
    obtain ⟨Q',hL,hΩ⟩:=Pantry.breakfast (o:=o) T hT hf hb hB0 hhX.good.labels hΨ (hs.symm ▸ (show 2 ≤ t by linarith only [hN])) ha (fun _=>hσ) hg hY hV (N:=Z0 n) hoP hXk (hs.symm ▸ h_l) (hs.symm ▸ h) (hs.symm ▸ Hq) (hs.symm ▸ hS') (fun i=> (Tour.bright (X) ‹C.Makes›.wilson N p n (hk.le.trans hm) i).ne') (spice_live U hp')
    · have hξ:0< ζ:=pow_pos he _; refine ⟨hξ,Q',⟨hL.cleared,hL.fettled,?_⟩,fun i=> ⟨(hΩ i).1,fun hi=>?_⟩⟩
      · have hc:=hL.grants; let Xk:=C₀.p.supportExponent-2; have ht': 1*(1:ℝ)≤1:=by norm_num
        apply hc.prune _ _ (slighter _ _ (w:=1) _ zero_le_one le_rfl) zero_le_one (show t-2+0 ≤ C₀.p.supportExponent-2 from by rw [add_zero,hs]) ht'; all_goals intros i; first | exact hξ| exact hξ.trans_le (hg' i) | exact (hg' i).trans_eq (one_mul _).symm
      exact ((hΩ i).2 hi).more (mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hξ (hg' i)) (by norm_num))
end YM.RG05Readout.Many
