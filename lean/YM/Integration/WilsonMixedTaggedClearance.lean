import YM.Integration.WilsonAllDateHarvestClearance
import YM.Integration.WilsonMixedTaggedSpend

/-! Each live resident supplies its own offset in its original compact test.
The full ward injects colours on every occupied word, and the funded
multicolour carton controls every such pair. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedClearance
open Function Filter Set Finset Lattice Wilson RG Marker Extra.Histories
open RG05Readout RG05Readout.Many RG05Readout.Native RG05Readout.Flatten RG05Readout.Pulse RG05Readout.Address
open PhysicalNext.Repeat.Legato WilsonMeasuredAdmission
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{b t per:ℕ}
variable {W:Type}
variable (o:W→Site (C.side b per))(s:W→ℕ)(F:W→Body)
set_option quotPrecheck false
local notation "E" => (fun _:W=>(1,false) : W → Motion)
local notation "q" => (fun z:ManyStem C o b=>F z.val.1)

theorem resident (bt:b ≤ t) (z:ManyStem C o t)
    (live:z∉shadow (Mine.tree o E) s (headings o E q) t):
    let A:=C.S.toDepth bt per
    ∃y∈Native.box,placeR A (A.residue z.val.2)+((A.count.val:ℝ)⁻¹) • y∈
      Native.box∩tsupport (F z.val.1).val := by
  intro A
  by_contra no
  apply live
  change Cap (s z.val.1+2) (headings o E q t z) 0
  rw [WilsonReportHarvestResidentChart.heading o F bt z]
  intro j _ y hy
  let p:=placeR A (A.residue z.val.2)+((A.count.val:ℝ)⁻¹) • y
  have grid:p∈Native.box:=mapsR A (C.S.toDepth_odd bt per) _ hy
  have absent:p∉tsupport (F z.val.1).val:=fun lies=>no ⟨y,hy,grid,lies⟩
  have vanishes:iteratedFDeriv ℝ j (F z.val.1).val p=0:=
    notMem_support.mp (fun seen=>absent (support_iteratedFDeriv_subset _ seen))
  rw [feeR,pulled,vanishes,smul_zero,norm_zero]

private theorem position (bt:b ≤ t) (z:ManyStem C o t) {J:ℕ} (near:separation (o z.val.1) 0 ≤ J)
    (margin:C.S.a b*(2*(J:ℝ)+1)<C.S.radius per) (y:E4):
    let A:=C.S.toDepth bt per
    C.S.place (o z.val.1)+C.S.a b • (placeR A (A.residue z.val.2)+((A.count.val:ℝ)⁻¹) • y)=
        C.S.place z.val.2+C.S.a t • y ∧
      ‖C.S.place z.val.2‖ ≤ C.S.a b*(2*(J:ℝ)+1) := by
  intro A
  have assembled:A.assemble (o z.val.1,A.residue z.val.2)=z.val.2:=by
    rw [←z.property bt];exact A.unpack_at _
  have place:=WilsonReportHarvestLeafGrid.placed bt (o z.val.1) near (A.residue z.val.2) margin
  rw [assembled] at place
  have size:(A.count.val:ℝ)≠0:=by exact_mod_cast A.count.property.ne_zero
  have scale:C.S.a b*((A.count.val:ℝ)⁻¹)=C.S.a t:=by
    rw [←C.S.embeds_scale A,mul_assoc,mul_inv_cancel₀ size,mul_one]
  exact ⟨by rw [smul_add,smul_smul,scale,←add_assoc,←place.1],place.2⟩

variable [DecidableEq W] [Fintype W]

theorem atDate (bt:b ≤ t) {J:ℕ} (near:o∈Pulse.area (C:=C) J)
    (margin:2*(C.S.a b*(2*(J:ℝ)+1))<C.S.radius per)
    {r η:ℝ}(rp:0 < r)(ep:0 < η)(funded:Pulse.buy C b per o (r*η/2) F)
    (room:C.S.a t*((((C.path.levels.budget t).B^2+1:ℕ):ℝ)) ≤ r*η/16)
    (roster:Census (W)):
    Clearance o E s (headings o E q) roster t := by
  intro v clean i hi j hj different
  let A:=C.S.toDepth bt per
  let B:=(C.path.levels.budget t).B
  let a:=C.S.a t
  have pos:0 < a:=C.S.a_pos _
  have within:∀v,separation (o v) 0 ≤ J:=by
    simpa only [Pulse.area,Finset.mem_filter,Finset.mem_univ,true_and] using near
  have cost:0 ≤ C.S.a b*(2*(J:ℝ)+1):=mul_nonneg (C.S.a_pos b).le (by positivity)
  have half:C.S.a b*(2*(J:ℝ)+1)<C.S.radius per:=by linarith only [margin,cost]
  have ai:i∉shadow (Mine.tree o E) s (headings o E q) t:=fun dead=>Set.disjoint_left.1 clean dead hi
  have aj:j∉shadow (Mine.tree o E) s (headings o E q) t:=fun dead=>Set.disjoint_left.1 clean dead hj
  obtain ⟨u,hu,atU⟩:=resident o s F bt i ai
  obtain ⟨v',hv,atV⟩:=resident o s F bt j aj
  have color:i.val.1≠j.val.1:=fun same=>different ((Finset.mem_filter.mp v.property).2.2 hi hj same)
  have distance:=funded i.val.1 j.val.1 color _ atU _ atV
  have pi:=position o bt i (within i.val.1) half u
  have pj:=position o bt j (within j.val.1) half v'
  change r*η/2 ≤ ‖(C.S.place (o i.val.1)+C.S.a b • _)-(C.S.place (o j.val.1)+C.S.a b • _)‖ at distance
  rw [pi.1,pj.1] at distance
  have short:‖C.S.place i.val.2-C.S.place j.val.2‖<C.S.radius per:=
    (norm_sub_le _ _).trans_lt ((add_le_add pi.2 pj.2).trans_lt (by linarith only [margin]))
  have center:‖C.S.place i.val.2-C.S.place j.val.2‖ ≤ 2*a*(separation i.val.2 j.val.2:ℝ):=
    (RG17.nativeShort C short).2
  have gap:r*η/2 ≤ 2*a*(separation i.val.2 j.val.2:ℝ)+2*a:=by
    apply distance.trans
    calc
      _ = ‖(C.S.place i.val.2-C.S.place j.val.2)+(a • u-a • v')‖ := by congr 1;abel
      _ ≤ _:=norm_add_le _ _
      _ ≤ 2*a*(separation i.val.2 j.val.2:ℝ)+(a+a):=add_le_add center
        ((norm_sub_le _ _).trans (add_le_add (room_B (C:=C) _ hu) (room_B (C:=C) _ hv)))
      _ = _:=by ring
  change B^2+1 ≤ separation i.val.2 j.val.2
  by_contra! close
  have upper:separation i.val.2 j.val.2 ≤ B^2:=Nat.le_of_lt_succ close
  have step:=mul_le_mul_of_nonneg_left (show (separation i.val.2 j.val.2:ℝ) ≤ ((B^2:ℕ):ℝ) by
    exact_mod_cast upper) (show 0 ≤ 2*a by positivity)
  change a*((B^2+1:ℕ):ℝ) ≤ r*η/16 at room
  push_cast at room step
  nlinarith only [room,step,gap,mul_pos rp ep]

theorem original (R:Run G) (simple:G.Simple) {K:ℕ} (large:5 ≤ K) {η:ℝ} (ep:0 < η):
    ∀ᶠ r:ℝ in 𝓝[>]0,let C:=R.family
      let t:=WilsonMeasuredWindow.stop C.path.levels simple K r
      ∀(b per J:ℕ)(_ : b ≤ t)(o:W→Site (C.side b per))(s:W→ℕ)(F:W→Body),
        o∈Pulse.area (C:=C) J → 2*(C.S.a b*(2*(J:ℝ)+1))<C.S.radius per →
        Pulse.buy C b per o (r*η/2) F → ∀roster:Census (W),
        Clearance o (fun _=>(1,false)) s
          (headings o (fun _=>(1,false)) (fun z:ManyStem C o b=>F z.val.1)) roster t := by
  filter_upwards [WilsonAllDateHarvestClearance.calendar R simple large ep,self_mem_nhdsWithin]
    with r room rp C t b per J bt o s F near margin buy roster
  exact atDate o s F bt near margin rp ep buy room roster


omit [DecidableEq W] [Fintype W] in
theorem mesh (R:Run G) (J:ℕ) :
    ∀ᶠ r in 𝓝[>] (0:ℝ),let b:=RG05Readout.crossLevel R.family.S r-1-1
      0 < r ∧ r ≤ R.family.S.a b ∧ ∀per:ℕ,
        2*(R.family.S.a b*(2*(J:ℝ)+1)) < R.family.S.radius per := by
  let S:=R.family.S
  have zoom:Tendsto (fun r:ℝ=>OPE.run r) (𝓝[>] (0:ℝ)) atTop := by
    simpa only [Function.comp_def,Real.log_inv,OPE.run] using
      (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have physical:OPE.RateIs (𝓝[>] (0:ℝ)) OPE.run id (-1) := OPE.loglife tendsto_id
  have cross:=RG05Readout.pace_crossing R.family.path.levels.fits.mesh zoom physical
  have reaches:=R.family.S.shrinks.comp (WilsonMixedTaggedSpend.lower R)
  have factor:0 < 2*(2*(J:ℝ)+1):=by positivity
  have fine:=reaches.eventually_lt_const (div_pos (S.radius_pos 0) factor)
  filter_upwards [self_mem_nhdsWithin,cross.2,fine] with r rp upper margin
  intro b
  refine ⟨rp,upper.2.trans (S.strictAnti.antitone (Nat.sub_le _ _)),?_⟩
  intro per
  have bound:2*(S.a b*(2*(J:ℝ)+1)) < S.radius 0:=by
    have bill: S.a b*(2*(2*(J:ℝ)+1)) < S.radius 0:=(lt_div_iff₀ factor).mp margin
    linarith only [bill]
  apply bound.trans_le
  change ((S.period 0).val:ℝ)/2 ≤ ((S.period per).val:ℝ)/2
  exact div_le_div_of_nonneg_right (by exact_mod_cast S.period_strict.monotone (Nat.zero_le per))
    zero_le_two

end YM.Integration.WilsonMixedTaggedClearance
