import YM.RG05Readout.Many.Film
/-!
# At test holes on the actual density polynomial

For m-opening keep all the ancestors. Every affected selection ALREADY
vanishes on the transform back on true density, using exact affine pulls
(and enough native test derivatives). At the root we really open for
subsequent mixed estimates; not replacing the vacuum. Using moods we
certify within Bud again.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
section dark
variable {G:Gauge} {S:Side}{d:ℕ}{V W:Type}[DecidableEq V][DecidableEq W][Fintype V][Fintype W]{R:Census V}{B:Census W}
lemma birth_dark {P:Rep G S}{F: V→ Config G S→ℂ} (D:Set V) (hx:∀ i∈D,F i=0) (U:Config G S) (j:R.Mode)(hp:¬Disjoint D (j.val:Set V)) : (birth R P F U).part j=0:=by
    let r:=fun i:V=>if i∈ D then (0:ℂ) else 1; let L:=feed r (id_licenses R); let Z:= Mach R (fun i=> F i U)
    have hz s:r s * F s U=F s U:=by
       unfold r; split
       next h=> simp [hx s h]
       next=> rw [one_mul]
    have he:L Z=Z:=by unfold L Z; rw [feed_mach]; simp [hz]
    unfold birth; let f:= Poly.pass Z
    have hV: f=temperV R D f :=by
         unfold f; change Poly.pass _= L (Poly.pass _); rw [YM.Multi.pass_map L Z (mute ..),he]; rw [he]; exact mute ..
    rw [Poly.part_smul,show Poly.pass _= temperV R D f from hV, temper_part,if_neg hp,mul_zero]
-- temper nat: D comprises entire preimages of disabled target marker. (License includes any old-old exclusions). Used BEFORE estimate with no zero claims on forbidden words.
omit [Fintype V][Fintype W] in
lemma temper_up {q:V→W}(h:License B R q) (l:V→ℂ)(S:Set W)(p:Poly R):temperV B S (feed l h p)=feed l h (temperV R (q ⁻¹' S) p):=by
    let L':= feed l h; let s:= q ⁻¹' S
    ext i; rw [temper_part, parts_of_feed, parts_of_feed]; split
    next hv=>
       refine sum_congr rfl (fun j _=>?_); unfold move; split
       next ht=> rw [Poly.part_send,Poly.part_send];split
                 next he=> rw [temper_part,if_pos ?_]; rw [he] at hv; exact Set.disjoint_left.mpr (fun a hp ha=> Set.disjoint_left.mp hv hp (mem_image_of_mem q (show a∈j.val from ha)))
                 next hz=> rfl -- maybe split rw both
       next=> rfl
    next he=>
       symm; refine sum_eq_zero fun j _=>?_ ; unfold move; split
       next ht=> rw [Poly.part_send];split
                 next hI=> rw [temper_part,if_neg ?_,mul_zero];
                           rw [hI] at he; obtain ⟨v,hv,h⟩:= Set.not_disjoint_iff.mp he; obtain ⟨v,hv',rfl⟩:=mem_image.mp h; exact Set.not_disjoint_iff.mpr ⟨v,hv,hv'⟩
                 next=>rfl
       next=>rfl
variable {C:Family G}{κ d' e x a:ℝ}{J:RG.Rep G S}{F:Frame G 0}{T:SectionData F}
lemma dormant {p:Tape G S}{o:Site S}{w z: Palette C d}(h: Printed C d J o κ p w z a){Y:Body}(hv:Cap (d+2) Y 0):p Y=0:=by
    obtain ⟨P,Q,h,hP,hR,rfl,hZ,hX,hw⟩:=h
    have hx(i:Letter d):readJ i 0 Y=0:= norm_le_zero_iff.mp (le_trans (fees d i box0 hv) (le_of_eq (mul_zero _)))
    simp_rw [LinearMap.add_apply,together,LinearMap.sum_apply,glyph_apply,hx,zero_smul,Finset.sum_const_zero,zero_add];
    have hQ : ∀ {Q:Tape G S} {a:ℝ}, Necklace (C.labels.level 0) (C.localSection 0) C.params J o κ d Q a→ Q Y=0:=by
       intro Q a H; induction H with
       | empty => rfl
       | chain f he hf q h h' hV ih=> simp [ih, norm_le_zero_iff.mp ((hf Y 0 hv).trans_eq (mul_zero _))]
    exact hQ h
lemma unlit (C:Family G)(n p d:ℕ)(q: Palette C d){Y:Body}(hv: Cap (d+2) Y 0) : entrance C d n p q 0 Y=0:=by
    unfold entrance; apply sum_eq_zero; intro i _; rw [show readJ i.1 0 Y =0 from norm_le_zero_iff.mp ((fees d i.fst box0 hv).trans_eq (mul_zero _)),zero_smul,smul_zero]
end dark
variable {G:Gauge} {C:Family G} {n m p N d:ℕ}{V: ℕ→Type}[∀ i,DecidableEq (V i)][∀ i,Fintype (V i)] {W:Type*}
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {j b k g:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "t₁"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "P!"=> C.side
local notation "Y"=> C.path.rep N p
local notation "L!"=> C.path.levels.clock.op
variable (A:Planner C p n V W) {H G':∀ i:ℕ,Census (V i)} (s:W→ℕ)
local notation "Λ"=>A.labelY
local notation "Φ"=>A.narrows
local notation "r₀"=>A.supportX
variable {F:∀ i:ℕ, Config G (C.side i p)→Poly (H i)}{U:∀ i:ℕ, Config G (C.side i p)→Poly (G' i)}
omit [(i:ℕ)→Fintype (V i)] in
lemma Replay.black (D:∀ i:ℕ,Set (V i))(hp:n≤b)(_hv:b≤ m)(hr:Replay (H:=H) A s hp m F N)
    (hX:Integrable (F m) (prior G _)) (ht:m≤N)
    (hA:∀ i:ℕ,∀ hi:b ≤ i,i < m → ∀ x: V (i+1), ((A.narrows i (hp.trans hi)) x).1∈ D i→ x∈ D (i+1))
    (hc:∀ U (j:(H m).Mode),¬Disjoint (D m) (j.val:Set (V m)) → (F m U).part j=0) {i:ℕ} (hi:b ≤ i)(hm:i≤ m) (U:Config G (C.side i p))(y:(H i).Mode)(hy:¬Disjoint (D i) (y.val:Set (V i))) : (F i U).part y=0:=by
    induction hm using Nat.decreasingInduction with
    | self=>exact hc U y hy
    | of_succ i hk ih=>
       have hL:= hr.live A s hp hX ht (hi.trans i.le_succ) hk
       obtain ⟨l,hR⟩:=hr.downhill (V:=V) i hi hk; let L:=Prod.fst ∘ ((A.narrows i (hp.trans hi))); let Z:= L ⁻¹' (D i)
       have hV(x): temperV (H (i+1)) Z (F (i+1) x)= F (i+1) x:=by
           ext j; rw [temper_part]; split; · rfl
           next ht=> rw [ih (hi.trans i.le_succ) x j (fun h' => ht (Set.disjoint_left.mpr fun x hx hq=> Set.disjoint_left.mp h' (hA i hi hk x hx) hq))]
       let z':=feed (fun i:V (i+1)=> if i∈Z then (0:ℂ) else 1) (id_licenses (H (i+1))) -- i shadowing H type? binder attr later
       let p':= (L! i p).push ((Y (i+1)).beta) (F (i+1))
       have hx : temperV (H (i+1)) Z (p' U)=p' U:= (congr_fun (amp_live z'.toLinearMap _ hL ((Z₀).transition_mass i p ((Y (i+1)).beta))) _).symm.trans (congr_arg (fun f=>(L! i p).push ((Y (i+1)).beta) f U) (funext hV))
       have hw : temperV (H i) (D i) (F i U)=F i U:=by rw [hR]; unfold downdraft; rw [temper_up]; exact congr_arg (feed _ _) hx
       have h:= congr_arg (fun x=> Poly.part x y) hw; change (temperV (H i) (D i) (F i U)).part _=(F i U).part y at h; rw [temper_part,if_neg hy] at h; exact h.symm
end YM.RG05Readout.Many
