import YM.RG05Readout.Capture.Line
import YM.OPE.Portfolio.Bookbind
/-!
# Application on rooted side

No requirement that input grouped polynomials are equivariant or choose
matching leaf expansions. For the view on *one* copy/root, recover canonical
charges and density jet in library's Probe. The rides for THAT copy hold.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Legato View
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge} {C:Family G} {N m p d:ℕ}{t:Motion}
section
variable {n:Side}{R:Rep G n}{P P':Three G n}{x:Site n}
noncomputable def eject (t:Motion)(x:Site n) : Site n:= (t.1⁻¹).act (-x) -- notation requires ()
lemma unplace (z:Site n): affine (Motion.backward t).1 (eject t x) (affine t.1 x z)=z:=by simp only [Motion.backward,eject, affine,Signed.act_add,Signed.act_neg]; simp
lemma rear : affine t.1 x (eject t x)=0:=by simp [eject,affine]
lemma Signpost.revokes (h: Signpost R (Motion.backward t) (eject t x) P P'): Signpost R t x P' P:=by
    have ht: MergeProof.twist t (Motion.backward t)=(1,false):=by rcases t with ⟨a,_|_⟩ <;> simp [MergeProof.twist,Motion.backward] -- cases
    refine ⟨by rw [h.trade,step_cycle,ht,rear, MergeProof.Ribbons.stepid],by rw [h.gate,step_cycle,ht,rear, MergeProof.Ribbons.stepid],by rw [h.lens,float_cycle,ht,rear, MergeProof.Ribbons.floatid]⟩ -- exact
lemma signpost_scales (h:Signpost R t x P P')(z:ℂ):Signpost R t x (z • P) ((scalar t z) • P'):=by
    have he(f:Goods G n): (scalar t z) • stepUp t x f= stepUp t x (z • f):=funext fun _=> (scalar_mul ..).symm
    refine ⟨?_, ?_,?_⟩
    · rw [show ((scalar t z) • P').fst=scalar t z • P'.fst from rfl, h.trade]; exact he _
    · rw [show ((scalar t z) • P').snd.fst=scalar t z • P'.snd.fst from rfl, h.gate]; exact he _
    change profile R.activities (scalar t z • P'.snd.2)= floatUp _ _ (profile R.activities (z • P.snd.2)); rw [profile_scale,profile_scale,h.lens]; exact funext (fun i=> he _)
end
local notation "Z!"=> C.path.levels
local notation "ℓ"=> C.path.S.block m
local notation "ρ"=> ((ℓ).val:ℂ)^d
local notation "Ld"=> Copper.ld C.path.levels m
local notation "S"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "O"=> C.path.levels.clock.op m p
local notation "λ!"=> (O).ratio
variable (h:C.Makes){A a B B':ℝ}{v: Bud C p m}{x:Site (C.side m p)}{P:Three G (C.side (m+1) p)}{D:Address.Rail C}(hc:Cater C D) (hm:m<N)
variable (w:PulseC)
local notation "o'"=> child C p m v
local notation "z'"=> (λ!).embed x
local notation "y'"=> affine t.1 z' o'
local notation "κ"=> D N p m hm
abbrev debit (C:Family G)(m d:ℕ)(a:ℝ):ℝ:= publicCost d (Copper.ld C.path.levels m)*(bling C.path.levels m*a)
local notation "T"=> debit C m d a
local notation "A₁"=> Many.headFee C p m v
include h hm hc
lemma upright (hp:Copper.SignedPrice C m p d N (D N p m hm) B B') (hD:d+3 ≤ (Z!).clock.J m)(hW: Priced d w 1) (he:Useful (M) P) (hY: MergeProof.Float.Blade (M) y' (P.snd.1) (profile ((M).activities) P.snd.2) 0 a)(ha:0≤a) :
    ∃ P':Three G (C.side (m+1) p),Signpost M t z' P' P ∧ ∃ (V:Tape G (C.side m p)) (f g:Palette C d), Course (d:=d) (D:=κ) o' ((glyph w P').comp A₁) V f g T T∧ size f ≤ T ∧
    ∀ (φ:Body)(s:ℝ)(π:(C.path.rep N p m).activities.Moves t.1 x), Cap (d+2) φ s → Ride O y' x κ ρ (scalar t (w (A₁ φ)) • P) (View.spin t π (V φ)) (T*s):=by
    let t':=Motion.backward t
    obtain ⟨π⟩:= (h.wilson.represents N p _ hm).good.labels.moves t'.1 (eject t z')
    let P':=View.spin t' π P; have ht:Signpost M t' (eject t z') P P':=View.spin_at ..
    have hR:= Signpost.revokes ht; have hz:Useful M P':=signpost_use h hm _ _ he
    have hP:= MergeProof.Ribbons.ManyCopies.Cadet.Studio.moved_blade t' (eject t z') y' hY π
    rw [scalar_z,← ht.gate,← ht.lens, show affine t'.1 _ _= o' from unplace o'] at hP
    let W:= w.comp A₁; let c:= bling (Z!) m; have hu:1 ≤ c:=Real.one_le_exp (Real.sqrt_nonneg _)
    have htf: Priced d W 1:=by
       intro φ s hy
       refine hW _ _ (Native.cap_aff _ (inv_nonneg.mpr (by positivity)) ?_ (dist_box C p m v) hy); exact inv_le_one_of_one_le₀ (by exact_mod_cast (ℓ).property)
    obtain ⟨U,f,g,hF,hS⟩:= cooled h hm (hc.throve d m N p hm hD) hu hp htf (Bud.personal ..) hz hP ha -- .. syntax
    have heq : (glyph w P').comp A₁=glyph W P':= LinearMap.ext fun _=>rfl
    refine ⟨P',hR,U,f,g, heq.symm ▸ hF,hS, fun φ q π hY'=>?_⟩
    have hτ:=hF.ready φ q hY'; have hr:= h.wilson.represents N p m hm.le; let q':= w (A₁ φ)
    obtain ⟨i₀,i₁,hC,hV⟩:= hc.tiers m N p hm
    have hU : Ride O y' (affine t.1 x 0) κ ρ _ (View.spin t π (U φ)) (T*q):=View.paid h hm hC.publishes.propagate (by unfold Motion.scalar; split; simp; rfl) hτ (Useful.smul (M) _ (scalar t q') he) (signpost_use h hm.le _ π hτ.tomorrow) (signpost_scales hR q') (View.spin_at ..)
    rwa [show affine t.1 x 0=x by simp [affine]] at hU
end YM.RG05Readout.Address
