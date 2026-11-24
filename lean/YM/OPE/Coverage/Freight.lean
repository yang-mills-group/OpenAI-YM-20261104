import YM.OPE.Coverage.Transit
import YM.OPE.Coverage.StressRates
import YM.Next.PHASE.Seats

/-! # Hilbert slab pricing of individual fields on dense measured shelves

The main field may repeat arbitrarily many times in a singleton-slab train;
there are only two coarse residues. No common fine scale required later if
separating several such slabs with their actual clearances. Still ahead of
coefficient matching; the estimates here don't assume a quantitative EFT.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.OPE.Coverage
open Next.UVStress Next.Phase Set Function Filter Extraction Table Ward Cells RG OS Word Climb Spec Maxwell
open scoped Topology NNReal ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge}
section Generic
variable {L:Register G} (S:Table L)
/-- Actual raw token pricing. Width with buffers at the fixed time plane;
the raw choice can depend on the wanted measurement radius but is used on
any such singleton word with these buffers. -/
structure Fare (s A:ℝ) (u : L.Token) : Prop where
    rad : 0<s
    pos : 0 < A
    ride : ∀ (V : Chamber S timeAxis) (x:E4)(e:ℝ≥0), ∀ H: Slab timeAxis e [(x,u)], buffer timeAxis s e [(x,u)] →
       ∃ P:V.GNS.H.Op, ‖P‖ ≤ A ∧ ∀ y, P (V.GNS.plant y)=V.GNS.plant (entering H y)
end Generic
variable {C:Family G}{S:Table C.book}{F:Extraction.Order}
private lemma ext_room (Q : Schedule) (k n : ℕ) : ∀ᶠ b in atTop, (n:ℝ)*(2*(3*Q.a b))<Q.a k := by
  apply (show Tendsto (fun b => (n:ℝ)*(2*(3*Q.a b))) atTop (𝓝 0) from by
    simpa only [mul_zero] using (((Q.shrinks.const_mul (3:ℝ)).const_mul (2:ℝ)).const_mul (n:ℝ))).eventually
    (gt_mem_nhds (Q.a_pos k))

lemma funded (H:C.Makes)(he:F.PointLimits C S)(HS : S.Hierarchy)(pp:CellHyp C F)
    (𝓛:Filter (ℕ×ℕ)) [𝓛.NeBot] (h𝓛:𝓛≤F.fuse){m k:ℕ}{A s:ℝ}{u:C.book.Token}
    (hM : C.S.a m < s/32) (hK:m≤k)(hR:20*C.S.a k < C.S.a m)
    (hi:Pass.Reading C 𝓛 u A k)(hA : 0<A): Fare S s A u:=by
   have hs : 0<s := by have hh:=lt_trans (C.S.a_pos _) hM; linarith
   refine ⟨hs,hA,fun V x e hE hg=>?_⟩
   let w:C.book.Word := [(x,u)]
   change Slab timeAxis e w at hE
   obtain ⟨d,hd,hQ,hD,hB⟩:= OS.narrow C.S w hs hE hg (List.cons_ne_nil _ _) hM
   change Slab timeAxis d w at hD
   have h : OS.QRead S A hD:= by
      intro v
      obtain ⟨e,ht⟩ := Ground.future_reach v
      obtain ⟨E,W,hW,t,ht',ht₁,ht₂⟩ := affordable ht
      obtain ⟨l,hl,hsep⟩ := ((eventually_ge_atTop k).and (C.S.shrinks.eventually (gt_mem_nhds ht'))).exists
      obtain ⟨g,K,Q,hQ',hq⟩ := rates pp E W
      obtain ⟨b,hb,hb',hb₀⟩ := ((eventually_ge_atTop l).and ((eventually_ge_atTop g).and
        (ext_room C.S l (2*v.val.length)))).exists
      let X := Q*(C.S.a b)⁻¹^K
      have hX : 0≤X := by unfold X; have hh := C.S.a_pos b; positivity
      refine ⟨X^(2*v.val.length),fun q => ?_⟩
      have he0(i)(hi:i∈(v.val:C.book.Word)) : Pass.Reading C 𝓛 i.2 X b:=
        ⟨fun _=>i.2.2,tendsto_const_nhds,((show ∀ᶠ z in F.fuse, Single C ⟨i.2.1,i.2.2⟩ X b z.1 z.2 from hq b hb' i.2 (hW i hi).1 (hW i hi).2).filter_mono h𝓛)⟩
      simpa only [w,List.length_singleton,one_mul] using
        (Pass.travel_fares H F 𝓛 h𝓛 S HS he hK hl hb hD hB hd v ht₂ q (hM.trans (by linarith only [hs])) hsep
         (by simpa [w] using (show 2*(2*(5*C.S.a k))< C.S.a m from by linarith only [hR])) hb₀ A X hX
         (fun i hi' =>by obtain rfl : i=(x,u) := List.mem_singleton.mp hi'; exact hi) he0)
   obtain ⟨P,hP,H_⟩ := OS.producer V hD HS h hA
   let u := e-d
   refine ⟨P.comp (V.flow.E u), (ContinuousLinearMap.opNorm_comp_le ..).trans
     ((mul_le_of_le_one_right (norm_nonneg _) (V.flow.shrinks _)).trans hP),fun x => ?_⟩
   rw [ContinuousLinearMap.comp_apply, ← V.atBirth, H_]; congr 1
   apply Subtype.ext; change linked timeAxis _ w _ = linked timeAxis _ w _; unfold linked
   simp only [OS.travel,raised,paths]
   rw [← add_smul,← NNReal.coe_add, tsub_add_cancel_of_le hQ]

variable (U:Final C F S) {N d j₀:ℕ}{μ:ℝ}{r:ℕ→ℝ}(p:Stored U r d N μ)
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field
local notation "fA" => p.maps
-- `cost_basis` buys a single frame slot, at full arbitrary slab placements
-- in the time direction, with slack taken from a sufficiently long tuple
-- (the actual requested operator word length here is just one). The large
-- price for unrelated future probes disappears under the 4n-th root.
lemma basis_fare (α:ℝ)(hα:0<α)(hμ:0<μ)(hd:j₀≤d)(hn:4≤N)(ht:Fine r)(hp:Tendsto (fun i=>p.path i/r i) atTop (𝓝 0))
       (q:Fin (Module.finrank ℂ (E j₀))):
    let v:= Module.finBasis ℂ (E j₀) q
    ∃ Z:ℕ→C.book.Token, ∃ X:ℕ→ℝ, RateLE atTop (fare r) X 0 ∧ ∀ᶠ i in atTop, Fare S (α*r i) (X i) (Z i) ∧ S.classTokens (Z i)=⟨j₀,fA i j₀ v⟩:= by
      intro v
      let t:Fin 4→ℕ:=fun _=>j₀
      let z:record C t:=fun _=>q
      have hg:∀ j:Fin 4, t j ≤ d:=fun _=>hd
      let w:=depthWord t z
      obtain ⟨η,A,B,hB⟩:=p.receipt.proof_ 4 hn t hg z
      have he0(i):∃ (Y:C.book.Ref j₀) (𝓛:Filter (ℕ×ℕ)), 𝓛.NeBot ∧ 𝓛≤F.fuse ∧ fA i j₀ v=S.project j₀ Y ∧
            Tendsto (fun h=> (p.wheel i).tones hg w h 0) 𝓛 (𝓝 Y):= by
         obtain ⟨𝓛,hNeBot,h𝓛,hV⟩:=p.coup i
         obtain ⟨x,hx,hEq⟩:=hV ⟨j₀,Nat.lt_succ_of_le hd⟩ v
         exact ⟨x,𝓛,hNeBot,h𝓛,hEq,hx⟩
      choose Y 𝓛 hb hF hEq he using he0
      have hGrow : RateLE atTop (fare p.path) A 0:=by
         refine RateLE.of_norm_le ((Stored.price_stripe U p).add (RateLE.const 1 (fare_large p.path p.fades)) (fare_large p.path p.fades)) ?_
         filter_upwards [hB.off.eventually (gt_mem_nhds zero_lt_one),hB.pos] with i hi ⟨ha,hb'⟩
         rw [Real.norm_of_nonneg ha, inv_eq_one_div]
         have hA' : (A i)^4 ≤ 1/(p.wheel i).σ := (le_div_iff₀ ((p.wheel i).stripe)).mpr hi.le
         have hh: A i ≤ A i ^ 4 + 1 := by
           rcases le_total (A i) 1 with h | h
           · linarith only [pow_nonneg ha 4,h]
           simpa using (show (A i)^1 ≤ (A i)^4 + 1 from le_trans (pow_le_pow_right₀ h (by decide)) (le_add_of_nonneg_right zero_le_one))
         linarith only [hA',hh]
      refine ⟨fun i=>⟨j₀,Y i⟩,fun i=> max 1 (A i),?_rate,?_⟩
      case _rate =>
        have HH: RateLE atTop (fare r) A 0:=fun b hb=> by
           filter_upwards [hGrow (b/2) (half_pos hb),meter_comparable p ht] with i hi he using hi.trans (Real.exp_monotone (by nlinarith only [he.2,hb]))
        exact (HH.norm.add (RateLE.const 1 (fare_large r ht)) (fare_large r ht)).of_norm_le (Eventually.of_forall fun i=> by
           rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans (le_max_left ..))]; exact max_le (by linarith only [norm_nonneg (A i)]) (by linarith only [Real.le_norm_self (A i)]))
      have hr : ∀ᶠ i in atTop,(p.wheel i).r / (2*μ) < α*r i/32:=by
         filter_upwards [hp.eventually (gt_mem_nhds (by positivity : 0<α/32*(2*μ)))] with i hi
         rw [p.spot]; exact ((div_lt_iff₀ (by positivity)).mpr (by linarith only [(div_lt_iff₀ (ht.1 i)).mp (show p.path i/r i < α/32*(2*μ) from hi)]))
      filter_upwards [hB.costs,hr] with i hi hr
      obtain ⟨m,k,hm,hK',hmk,hA⟩:=hi.crude
      have h₀:=Next.UVStress.ample _ hA
      letI:=hb i
      refine ⟨funded U.room.cutoff U.room.generic U.room.kernel U.room.copies (𝓛 i) (hF i) (hm.trans hr) hK'
             (by norm_num only [Nat.cast_ofNat] at hmk; linarith only [hmk,C.S.a_pos k]) ⟨_,he _,?Payments⟩ (?positive),Sigma.ext rfl (heq_of_eq (hEq i).symm)⟩
      case positive => exact zero_lt_one.trans_le (le_max_left ..)
      exact h₀.filter_mono (hF i) |>.mono fun z hz=> ⟨hz.1,fun _ j=> ⟨(fixup C ((hz.2 0 j).1) (le_max_right ..)),(hz.2 0 j).2⟩⟩
end YM.OPE.Coverage
