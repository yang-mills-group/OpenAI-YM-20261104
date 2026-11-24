import YM.SignedWilsonExpansion.Chron.Comet
import YM.Integration.WilsonOriginalStarLaurentWallet
import YM.Integration.WilsonOriginalProjectedCurvatureAtom
/-!
Primary visa consumes the literal atom declaration and rank-leading stencil,
not a covariance sensor. Leg budget power scales are at K, unchanged by
re-timing. Used for (20),(24)--(25),(27). Do not identify phase at this step.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.Liner
open Function Matrix Lattice RG Laurent Bloch Gauge
open WilsonCoeffUV WilsonCoeffUV.Blue FreeResolvent Tree WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Power
open WilsonCoeffUV.Bank WilsonCoeffUV.Soil Exterior Source WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Mer.Xa
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark Lattice Laurent Labels Precision PowerSeries
open WilsonCoeffUV.Bank.Mosaic
open PhysicalNext.Repeat.Legato Wilson Stationary Finset
open OriginalMarkedSourceComet IndependentSourcePathFamily
open ActualRunCurvaturePackets
open ActualRunGradedKernels (rank section_valuation)
open WilsonOriginalStarLaurentWallet (Socket lag shape)
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{J:Type}{d k f r ℓ h:ℕ}(D:J→ℕ) [DecidableEq J]
variable (R:Run G)(d:ℕ){n:Side}(pt:Chamber)
local notation "F"=> ( R.family.labels.level d )
local notation "Ŝ"=> (R.family.localSection d)
abbrev Mono (i:(R.family.labels.level d).Index):= (((ofRun R d).data.shape i).support : Type)
variable (j:J)(c:Chamber)
-- before any cutoff.R.Frame
section core
variable (i:(R.family.labels.level d).Index)(s:Mono R d i)
private abbrev length (s:Mono R d i):=s.val.sum fun _ r=>r
private abbrev pigment (s:Mono R d i) (k:Fin (length R d i s)):= (NativeCurvatureTensor.word s.val k).2 -- wrong namespace?
private abbrev wing (s:Mono R d i) (k:Fin (length R d i s)) := (ofRun R d).data.columns i (NativeCurvatureTensor.word s.val k).1
private abbrev atomE (s:Mono R d i) := WilsonOriginalProjectedCurvatureAtom.atom (pigment R d i s) (wing R d i s)
private abbrev plainA (G:Gauge):Atom G 0:= ⟨Fin.elim0,fun _=>1⟩

def spurS (D:ℕ) (p:Chamber)(s:Socket R d):Seed G D:=
   ⟨length R d _ s.2, length R d _ s.2 - lag R d s, (atomE R d _ s.2).leg, pigment R d _ s.2,1,Complex.reCLM,knob D,p⟩
def plainS (G:Gauge)(D:ℕ) (p:Chamber):Seed G D:= ⟨0,0,(plainA G).leg, Fin.elim0,1,Complex.reCLM,knob D,p⟩
abbrev Cursor := Unit ⊕ Socket R d
def petS (D:ℕ)(p:Chamber): Cursor R d → Seed G D:=Sum.elim (fun _=>plainS G D p) (spurS R d D p)
lemma curveS (i:Socket R d) : (lag R d i)+(spurS R d h c i).head=(spurS R d h c i).rank :=by
    have hv : lag R d i ≤ (length R d i.1 i.2):= (ofRun R d).data.low i.1 i.2.val i.2.property; change _+(_-_)=_; change _≤ (spurS R d h c i).rank at hv; exact Nat.add_sub_of_le hv
lemma paysS (s:Cursor R d): (petS R d h c s).rank ≤ d+(petS R d h c s).head:=by
   cases s with
   | inl => exact Nat.zero_le _
   | inr s=> change (spurS R d h c s).rank≤_; rw [←curveS]; exact Nat.add_le_add_right (value_le F s.1) _
lemma atom_unmask (G:Gauge)(U:Config G n)(x:Site n): (plainA G).unmasked U x=1:=by simp [plainA, Atom.unmasked, Atom.poly]
omit [DecidableEq J] in
lemma petalE : Ur D j (spurS R d (D j) c ⟨i,s⟩)=atomE R d i s:=by
    unfold Ur; dsimp only [spurS,colour]; congr; ext1 k; rw [one_mul]; rfl
omit [DecidableEq J] in
lemma petal₀ : Ur D j (plainS G (D j) c)= plainA G:=by
    unfold Ur; dsimp only [plainS,colour,plainA]; congr; ext1 i; rw [one_mul]; change ( (∫ g:G.El, _ ∂ G.probHaar ):ℂ).re=_; simp
-- key scalar reconstruction from ordinary actual sections
private lemma testL (x:ℂ)(L:ℂ→ₗ[ℝ]ℝ)(b:ℝ): L (x*(b:ℂ))= L x * b:=by
    rw [mul_comm x,← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
lemma Basis_truth {n:Side}(V:Config G n)(x:Site n)(b:ℂ)(L:ℂ→ₗ[ℝ]ℝ):
    L b * ActualStencilCylinder.observed Ŝ (Pi.single i 1) n x V= ∑ j:Mono R d i,L (b*shape R d ⟨i,j⟩)*(atomE R d i j).unmasked V x:=by
    rw [←testL,ActualStencilCylinder.observed_complex Ŝ (R.makes.sections d) i .., placed_basis (ofRun R d),basisValue, Finset.mul_sum,map_sum,← Finset.sum_coe_sort] -- adjust args
    refine Finset.sum_congr rfl fun i _=>?_ ; rw [← mul_assoc, ← testL, show ((atomE _ _ _ _).unmasked _ _ :ℂ) = _ from WilsonOriginalProjectedCurvatureAtom.unmasked ..]; rfl
lemma loom_jetPrice {U:Type}[Fintype U]{g:Lawn U→ℝ}(z:Green g)(K:ℝ): jet (K • g)= K • jet g:=by rw [show K • g=(fun _=>K)*g from rfl,jet_mul contDiffAt_const z,jet_const,← real_alg, Algebra.smul_def]
-- first at mark zero
lemma basis_earned (u:ℂ)(L:ℂ→ₗ[ℝ]ℝ)(n:Side):
    L u • Blue.flash ((Looms.literal Ŝ i).1 n)=
     ∑ f:Mono R d i,L (u*shape R d ⟨i,f⟩) • Blue.flash ((mount D j (spurS R d (D j) c ⟨i,f⟩) 0).1 n):=by
    let t:= rank R d i; let W:= fun (f:Mono R d i)=> L (u*shape R d ⟨i,f⟩); let Y(f:Mono R d i):= meter (atomE R d i f) (0:Site n)
    apply mul_left_cancel₀ (a:= PowerSeries.X^t) (pow_ne_zero _ X_ne_zero)
    rw [mul_smul_comm,Looms.mantel Ŝ (section_valuation R d) (R.makes.sections d),Finset.mul_sum]
    have ht (f:Mono R d i): Green (Y f):=(meter_hot ..).contDiffAt
    have hx : L u • Plies Ŝ i n=∑ f,W f • Y f:=by
       funext z; rw [ Finset.sum_apply ]; simp only [Pi.smul_apply, smul_eq_mul]; dsimp only [Y, W, meter]; simp only [Mosaic.mantle_input]; exact Basis_truth R d i (mantle z) 0 u L
    rw [← loom_jetPrice (innu Ŝ R.family.params (R.makes.sections d) i n),hx,jet_sum _ (fun i=> W i • Y i) (fun i _=> ContDiffAt.const_smul (W i) (ht i))]; apply Finset.sum_congr rfl; intro f _
    rw [mul_smul_comm,loom_jetPrice (ht f), show t=lag R d ⟨i,f⟩ from rfl, shot D j (spurS R d (D j) c ⟨i,f⟩) rfl (curveS R d c ⟨i,f⟩), map_zero,petalE]; rfl
lemma steady (v:Era G ℝ) : shifted v 0=v:=by
    unfold shifted; apply Prod.ext; · funext n i j x; simp [Mer.skewV,revolve,jog,comp_def]
    funext i j x; simp [Mer.skewV,revolve,jog,comp_def]
lemma mounted (T:Seed G (D j))(o:Cover): mount D j T o=shifted (mount D j T 0) o:=by
   change shifted (tuftV (touch (lamp D) {j}) (tuftV (petal D j) (volumeR (current (Ur D j T) (claim _ T.knob T.point)) T.head))) o=shifted (shifted (tuftV (touch (lamp D) {j}) (tuftV (petal D j) (volumeR (current (Ur D j T) (claim _ T.knob T.point)) T.head))) 0) o; rw [steady]
lemma pier_anthem₀ : mount D j (plainS G (D j) c) 0=Looms.literal (R.family.localSection d) 0:=by
    apply flash_recover (certifiedL D j _ (paysS (h:=D j) R d c (.inl ())) _) (Looms.strength Ŝ (section_valuation R d) (R.makes.sections d) le_rfl); intro n
    have h:=shot (r:=0) D j (plainS G (D j) c) rfl rfl n 0; rw [petal₀,pow_zero,one_mul] at h; change Blue.flash ((mount D j (plainS G (D j) c) 0).1 n)= jet (meter (plainA G) (wrap n 0)) at h; rw [show meter (plainA G) ((wrap n) 0)=fun _=>1 from funext (fun _=>atom_unmask ..), jet_const] at h; change Blue.flash ((mount D j (plainS G (D j) c) 0).1 n)=_; rw [h, Looms.unity Ŝ (section_valuation R d) (R.makes.sections d)]; change _= Blue.flash (uband 1); rw [uband_flash]; simp [realS] -- lint
-- equality pulls arbitrary real tests, no assumption ℂ-linear power reset
lemma pier_anthem (u:ℂ)(L:ℂ→ₗ[ℝ]ℝ):
    L u • Looms.literal Ŝ i = ∑ f:Mono R d i,L (u*shape R d ⟨i,f⟩) • mount D j (spurS R d (D j) c ⟨i,f⟩) 0 :=by
    have ht:Auth d (Looms.literal Ŝ i):= Looms.strength Ŝ (section_valuation R d) (R.makes.sections d) le_rfl
    have hv (s: Mono R d i):Auth d (mount D j (spurS R d (D j) c ⟨i,s⟩) 0) := certifiedL D j _ (paysS (h:=D j) R d c (.inr ⟨i,s⟩)) _
    let W(f: Mono R d i):=L (u*shape R d ⟨i,f⟩); apply flash_recover (ht.μ _) (Auth.sum (fun i (_:i∈Finset.univ)=>(hv i).μ (W i)))
    intro n; simp only [Prod.smul_fst, Pi.smul_apply,Prod.fst_sum,Finset.sum_apply]
    rw [flash_mu _ (ht.span n), basis_earned D R d j c i u L n,flash_term (P:=fun j₁:Mono R d i=> W j₁ • (mount D j (spurS R d (D j) c ⟨i,j₁⟩) 0).1 n) _ (fun i _=> show shellK d _ from ((hv i).μ (W i)).span n)]; exact Finset.sum_congr rfl (fun i _=> (flash_mu _ ((hv i).span n)).symm)
end core
-- scalar at the actual K. independent powers do not retime the prefix `g/θ`
def stick (g θ:ℝ)(x:(R.family.labels.level d).Coeff): Cursor R d → ℂ
   | .inl _=> x 0
   | .inr j=> WilsonOriginalStarLaurentWallet.coefficient R d g θ ((R.family.labels.level d).core x) j
def life (g θ:ℝ)(x:(R.family.labels.level d).Coeff):= (R.family.labels.level d).scaled (g/θ) x

section outside
lemma life_solo (g θ:ℝ)(x:(R.family.labels.level d).Coeff)(L:ℂ→ₗ[ℝ]ℝ):
   ∑ i:(R.family.labels.level d).Index,L ( life R d g θ x i ) • Looms.literal Ŝ i=
   ∑ f:Cursor R d,L (stick R d g θ x f) • mount D j (petS R d (D j) c f) 0:=by
   let W:=fun (i:(R.family.labels.level d).Index)=> (Complex.ofReal ((g/θ)^rank R d i)); let P:=(R.family.labels.level d).core x
   change _=∑ f: Unit ⊕ (Socket R d),_; rw [Fintype.sum_sum_type,Fintype.sum_unique (f:=fun a:Unit=> L (stick R d g θ x (.inl a)) • mount D j (petS R d (D j) c (.inl a)) 0),Fintype.sum_sigma]
   change _= L (x 0) • mount D j (plainS G (D j) c) 0 + ∑ i:(R.family.labels.level d).Index, ∑ f:Mono R d i, L ((W i*P i)*shape R d ⟨i,f⟩) • mount D j (spurS R d (D j) c ⟨i,f⟩) 0
   simp_rw [←pier_anthem D R d j c]; rw [pier_anthem₀ D R d]
   let T (i:(R.family.labels.level d).Index):=L ( life R d g θ x i) • Looms.literal Ŝ i; let Y(i:(R.family.labels.level d).Index):= L (W i*P i) • Looms.literal Ŝ i
   have h(t:(R.family.labels.level d).Index): life R d g θ x t= W t*x t:=rfl
   change (∑ i,T i)= _+(∑ i,Y i); apply (sub_eq_iff_eq_add).mp; rw [← Finset.sum_sub_distrib]; rw [Finset.sum_eq_single 0]; swap; · intro i _ hi; unfold T Y; rw [h,show P i=x i from update_of_ne hi ..,sub_self]
   swap; · simp
   unfold T Y; rw [h,show P 0=0 from by simp [P,Frame.core],mul_zero,map_zero,zero_smul,sub_zero,show W 0=1 from ?_,one_mul]
   unfold W; rw [show rank R d 0=0 from Xa.wr_unitH _, pow_zero,Complex.ofReal_one] -- check wr_unit
lemma shift_ν {P:Era G ℝ}(o:Cover)(a:ℝ): shifted (a • P) o= a • shifted P o:= rfl
lemma life_shift (o:Cover)(g θ:ℝ)(x:(R.family.labels.level d).Coeff)(L:ℂ→ₗ[ℝ]ℝ):
   ∑ i:(R.family.labels.level d).Index,L ( life R d g θ x i ) • shifted (Looms.literal Ŝ i) o=
   ∑ f:Cursor R d,L (stick R d g θ x f) • mount D j (petS R d (D j) c f) o:=by
   have he:=congr_arg (shifted · o) (life_solo D R d j c g θ x L); simp only [shifted_gather,shift_ν,← mounted] at he; exact he
end outside
end YM.Integration.Liner
