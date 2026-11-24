import YM.RG05Readout.Shadows.Loom
/-!
# Initial normalization in anchored Tape at n and Manifest

This is after true transmission including the step from a grouped b-root
(b=n+1). Purchase prices do not fix the represented log/K labels; choose
one on the product alone. Establish same at the inspected cell-coordinate
ports for *any* alternative presentation which is inhabited (not assuming
that from equal density).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N m n b p d:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ}{x e E e':ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op
local notation "ζ"=> C.S.block
local notation "F₀" => Palette C d
local notation "S₁" => C.S.scale
local notation "κ"=> kappa C.path
local notation "ℓ"=> Copper.ld C.path.levels
local notation "ν"=> C.path.levels.clock.J
variable (hw:Awake D B b d) (hv: Spine D B h b p d N V S)
local notation "v₁"=> wrap_price d C * Trace.Physical.Germ.wraps ((R₀ n).p) (C.side n p)
section pure
variable (P:Tape G (C.side n p))(X:Palette C d)
include h hw hv
noncomputable def bid (C:Family G) (n _d:ℕ)(x:ℝ):ℝ:= (1+2*(Copper.ld C.path.levels n))*x -- d parameter needed? remove
local notation "J"=> bid C n d
lemma cut_attain (hm:b ≤ n)(hN:n<N){Y:Palette C d}(hp:Printed C d (R₀ n) 0 (κ n) P X Y x)(hX:size X≤x): size Y ≤ 2*x ∧ ∃ z, Printed C d (R₀ n) 0 (κ n) (P-V n Y) z 0 (bid C n d x):=by
    have hQ:=hw.toll p n N hm hN; obtain ⟨s,K,c,β,T,Q,H,hT,hX',hu,hW⟩:=hQ.author
    have he:= (H.cursor.sense d le_rfl)
    obtain ⟨hb,-⟩:= max_le_iff.mp hu
    have hx:v₁≤1:=by rw [(h.wilson.represents N p n hN.le).vac]; exact hb.trans (thin_one ..)
    have hy:size Y≤2*x:= (size_compare Y X).trans ((add_le_add hX (le_trans (wraps_paid d C hp he.order he.power) (mul_le_of_le_one_left hp.nonneg hx))).trans_eq (two_mul ..).symm)
    obtain ⟨z,hz⟩:= (hv.legal n hm hN.le).capacity0 (-Y); rw [size_neg] at hz; have h':=hp.addP hz (h.wilson.represents N p n hN.le).good he.order he.power; rw [map_neg,add_neg_cancel] at h'
    refine ⟨hy,X+z,?_⟩; rw [sub_eq_add_neg]; apply h'.grow; unfold bid; have hB:B d n ≤ ℓ n:= (le_add_of_nonneg_left (show 0≤ B d (n+1) from (zero_le_one.trans hQ.pos.1))).trans hQ.caps; linarith only [mul_le_mul hB hy (size_ge Y) (zero_le_one.trans (lamp_nn ..))]
structure Signature (C:Family G)(p b n N d:ℕ) (h:C.Makes) (D: Address.Rail C) (V: Sight C d p) (T:Native.Body→ Goods G (C.side n p)) (E:ℝ)(Y:ℕ→ Palette C d)(X:∀ i:ℕ,Tape G (C.side i p)):Prop where
   basis : ∃ P:Tape G (C.side n p), pulseOut P=T ∧ X n = P-V n (Y n)∧ ∃ z, Printed C d (C.path.rep N p n) 0 (kappa C.path n) P z (Y n) E ∧ size z ≤ E
   pays : size (Y n) ≤ 2*E
   rolls : Halo D (eC:=h) b b n p N d V Y X (bid C n d E)
variable {Z:Palette C d}
lemma chamber (hm:b ≤ n)(hN:n<N)(hz:Printed C d (R₀ n) 0 (κ n) P X Z x)(hX:size X≤x) : ∃ Y X', Signature C p b n N d h D V (pulseOut P) x Y X':=by -- Z undeclared
   obtain ⟨hp,Hx⟩:=cut_attain h hw hv P X hm hN hz hX
   obtain ⟨Y,X',hY,hF,hT⟩:= liftH h hw hv le_rfl hm hN.le (P-V n Z) Z Hx
   exact ⟨Y,X',⟨P,rfl,by rw [hF,hY],X, hY.symm ▸ hz,hX⟩,(by rw [hY];exact hp),hT⟩
variable {P X}
-- equivalence on VAL only
omit h hv in
lemma germ_eyelet {F P:Tape G (C.side m p)} {u z a b':Palette C d} (hF:Printed C d (R₀ m) 0 (κ m) F u z x)(hr: Printed C d (R₀ m) 0 (κ m) P a b' e) (hp : b ≤ m)(hn:m<N) (he:pulseOut F=pulseOut P) : z=b':=by
   obtain ⟨s,K,c,β,T,Q,H,U⟩:= (hw.toll p m N hp hn).author
   exact hF.survives hr (fun i=>⟨s,H.cursor.sense _ (Nat.sub_le ..)⟩) (fun i=> EventuallyEq.of_eq (congr_fun he (Native.line i)))
-- signature origin for alternative presentation
variable {X':∀ i:ℕ,Tape G (C.side i p)} {F:Body→ Goods G (C.side n p)} {Y:ℕ→ Palette C d}
lemma roots_same (hm:b ≤ n)(hN:n<N)(ht : Signature C p b n N d h D V F E Y X') (P:Tape G (C.side n p)) (hc:pulseOut P=F) {A Q:Palette C d}(hp : Printed C d (R₀ n) 0 (κ n) P A Q x)(hX:size A ≤ x):Q=Y n ∧ pulseOut (P-V n Q)=pulseOut (X' n) ∧ ∃ z, Printed C d (R₀ n) 0 (κ n) (P-V n (Y n)) z 0 (J x):=by
   obtain ⟨X,hY,hP,W,hT,hR⟩:= ht.basis
   have hi:= germ_eyelet hw hp hT hm hN (hc.trans hY.symm)
   refine ⟨hi,?_,?_⟩
   · rw [hi,hP]; have hm(P':Tape G (C.side n p)):pulseOut (P'- V n (Y n))= pulseOut P'- pulseOut (V n (Y n)):=rfl; rw [hm,hm,hc,hY]
   rw [← hi]; exact (cut_attain h hw hv P A hm hN hp hX).2
-- G frame counted in propagation for signatures: actual M in report units separate. initialized launch vector scaled elsewhere. Here returns normalized threshold vector.
omit hw in
lemma codifies (hm:b ≤ n)(hN:m≤N)(hn:n ≤ m)(hJ:12 ≤ ν b)(hr:Signature C p b n N d h D V F E Y X') : let z:= finer S hn (Y n - advances S Y b n)
    -- m capture≤ etc. produce exact multi marker vector comparison bound
    size z ≤ stringCost C hn*(2*E+20* J E):=by
    intro z
    apply (hv.inverse_cost hm hn hN _).trans (mul_le_mul_of_nonneg_left _ (zero_le_one.trans (Many.stampCosts hn))); rw [sub_eq_add_neg]
    apply (size_add ..).trans; rw [size_neg]; apply add_le_add hr.pays
    have hp' := hr.rolls.empty n hm le_rfl; obtain ⟨θ,hθ⟩:=hp'; have hz := hθ.nonneg; rw [tab_one] at hz
    have he:= overture h hv hJ (hn.trans hN) hz hr.rolls.spends hm le_rfl; rwa [tab_one] at he
end pure
end YM.RG05Readout.Shadow
