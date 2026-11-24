import YM.RG05Readout.Shadows.Ewe
/-!
# Universal terminal invoice on physical rendering families

Market support from finest-point certificates still needed in physical
step issuance. Through this port, price in COPIER ratio.Read computes genuine
normalized value branch. No correlation binding to Fk in this checkpoint.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address Many Pressure
open Legato Bandage Next.Rank.Station Accent Marker Menu Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N m n b p d j:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ}{x e E e':ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op
local notation "ζ"=> C.S.block
local notation "ν"=> C.path.levels.clock.J
local notation "κ"=> kappa C.path
local notation "Z₀"=> C.path.levels.budget
local notation "w₀"=> focus C E n
variable (hw:Awake D B b d)(hv:Spine D B h b p d N V S) {H:∀ i:ℕ,Tape G (C.side i p)} {Y:ℕ→ Palette C d}
variable {I:ℕ→Type}{J:Type}[∀ i,DecidableEq (I i)][∀ i,Fintype (I i)] (A: Planner C p b I J) (F:∀ i,I i→Body){G':∀ i,Census (I i)}
local notation "V'"=>Aura (S:=S) (V:=V) (N:=N) (n:=n) H Y A F (G':=G')
variable {f:∀ i:ℕ,Config G (C.side i p)→Poly (G' i)}
local notation "e'"=> (Z₀ b).supportExponent
abbrev salary (C:Family G)(b d:ℕ):= 2*harvestCost C d b
include h hw
lemma terminal (hb : b ≤ n)(hN:n<N)(hP:∀ i:I b,Cap (d+2) (F b i) 1)(hp:V' b (f b) E e')(hE:0<E) (s:(G' b).Mode) (M:ℂ)
   (he:(∫ U,(f b U).part s∂prior G _)=(Wilson.partition G (C.side N p) (C.beta N p):ℂ)*M) : ‖M‖*((focus C E n b)^ s.val.card) ≤ Real.exp ((Fintype.card (Site (C.side b p)):ℝ)* Vac.treasury C.path.levels b+ Fintype.card (I b)*(2*salary C b d+2)):=by
    obtain ⟨P,S,hA,hB⟩:= hp.ship; let x:=w₀ b; let t:=harvestCost C d b; have hw':0 < x:=focus_ge hE
    let R:= R₀ b; have hr:= h.wilson.represents N p b (hb.trans hN.le)
    let M' j U:= coinCost (R) (P j) U
    have hx(j:I b) (U): x * M' j U ≤ salary C b d:=by
       obtain ⟨h,⟨v,hV⟩,hS⟩:= hB j
       simp only [adv_base,map_zero,add_zero] at hS
       let s':=tab C E n b
       have ht : size v ≤ s':= by
          obtain ⟨s,K,c,β,T,Q,H,hT,hX',hu,-⟩:= (hw.toll p b N le_rfl (lt_of_le_of_lt hb hN)).author
          have he:= (H.cursor.sense d le_rfl)
          obtain ⟨hz,-⟩:= max_le_iff.mp hu
          have hh := wraps_paid d C hV he.order he.power; rw [zero_sub,size_neg,hr.vac] at hh; exact hh.trans (mul_le_of_le_one_left hV.nonneg (hz.trans (thin_one ..)))
       have hy:0 ≤ t:=by unfold t harvestCost colCash; exact mul_nonneg (add_nonneg zero_le_one (feepos _|>.le)) (add_nonneg (by norm_num) (zero_le_one.trans (Stage.columns_ge _)))
       have hK: M' j U ≤ t*(2*s'):= by
          unfold M'; rw [coin_after (A.motion (A.labelY b j)) (A.supportX b j) _ hS]; exact (priced ‹C.Makes› hw (hb.trans hN.le) hV (hP j) _).trans (mul_le_mul_of_nonneg_left (by linarith only [ht]) hy)
       let g:= ((Z!).clock.hatBeta b)^4; have hg: 1≤ g:= one_le_pow₀ ((Z!).fits.delayed _|>.le)
       have hf: 0 < s':= mul_pos (Real.exp_pos _) hE; refine (mul_le_mul_of_nonneg_left hK hw'.le).trans ?_; change (g*s')⁻¹*_ ≤ 2*t; field_simp; nlinarith only [mul_le_mul_of_nonneg_right hg hy] -- risk
    let w₁:=fun _:I b=> x
    have hs: Vault w₁ (fun i=>(P i).snd.fst) (fun i=> profile R.activities ((P i).snd.2)) (salary C b d) (salary C b d):=by
        refine ⟨fun i U=>(mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=> norm_nonneg _))) hw'.le).trans (hx i U),fun i U=>?_⟩
        rw [← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hw'.le).trans (hx i U)
    have hr':= spiker C N b p ‹C.Makes› s M (hb.trans hN.le) (fun _=>hw') hA.grants hs hA.cleared he
    unfold Poly.toll at hr'; rw [Finset.prod_const,show _ = 2*salary C b d+2 from Eq.symm (show _=salary C b d+salary C b d+ 2*1 from (by ring))] at hr'; exact hr'
-- Descending traveler
section
include hv
local notation "A!"=> A.supportX
local notation "Q!"=> apron C.path.levels
variable (ht:Halo D (eC:=h) b b n p N d V Y H e)(hS:Storage C D)
include ht hS
lemma dawns (_hb : b ≤ n)(hN:n ≤ N)(hF:PreparedA A F b n le_rfl)(hP:∀ i:I b,Cap (d+2) (F b i) 1) (hp:V' n (f n) E ((Z₀ n).supportExponent)) (hE:0<E) (hz:e ≤ E) (ho:∀ i:ℕ,b ≤ i→ i < n → Occupancy (A! (i+1)) (Q! i)∧ Occupancy (((Ω i p).ratio.parent) ∘ (A! (i+1))) (Q! i))
    (hR:Replay (N:=N) (H:=G') (b:=b) A (fun _=>d) (le_refl b) n f)
    (hg:∀ i, b ≤ i→ i < n → Drake (G' (i+1)) (Z₀ i).B (((Ω i p).ratio.parent)∘ A! (i+1))) (hY:∀ i,b ≤ i→ Pin C i d): ∀ i:ℕ,b ≤ i → i≤ n → V' i (f i) E ((Z₀ i).supportExponent):=by
    intro i hi hk; induction hk using Nat.decreasingInduction with
    | self=> exact hp
    | of_succ i hi' ih =>
        obtain ⟨z,h⟩:= (hR.downhill (V:=I) i hi hi'); rw [h]; exact Shadow.forecast ‹C.Makes› hw hv H Y ht A F hS (f (i+1)) hE hz hi hi' hN (hY b le_rfl).lit.1 (cap_lives A (fun _=>d) F le_rfl hi hi'.le hF hP) (hF _ hi hi') z (ho i hi hi').1 (ho i hi hi').2 (hg i hi hi') (ih (hi.trans i.le_succ)) (by linarith only) (hY i hi)
end
end YM.RG05Readout.Shadow
