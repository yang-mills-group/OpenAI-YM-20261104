import YM.RG17.Avenue
import YM.MergeProof.North.Vert
import YM.Push.ABSOLUTE_SUMS.Animals

/-!
 Geometry for actual glued correlation stencil (selected D0 readout).
 In four-dimensional lengths. Canonical seam convention. No separated
 tuple hypothesis on ambient grid. Need short diameter for pair lower &
 upper estimates; independent of absolute location.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open OPE OPE.Orbits
open Lattice Extraction Filter Set Function MeasureTheory Spec Table Next.Rank Next.Rank.Station
open Push.AbsoluteSums.Animals
open scoped Topology Classical BigOperators
variable {G:Gauge}(C:Family G){f:Extraction.Order}{S:Table C.book}{b N p:ℕ}{n:ℕ}

lemma shortWay {x y:Site (C.side N p)} (h:‖C.S.place x-C.S.place y‖ < C.S.radius p):
    C.S.place (x-y)= C.S.place x-C.S.place y:=by
    let d:=lift x-lift y
    have hp:=C.S.a_pos N
    have hz: lift (x-y)=d:=by
       apply lift_eq_iff.mpr; refine ⟨?_,fun i=>?_⟩
       · simp [d]
       have hs := lt_of_le_of_lt (PiLp.norm_apply_le (C.S.place x-C.S.place y) i) h
       change ‖C.S.a N * ((lift x i:ℤ):ℝ) - C.S.a N * ((lift y i:ℤ):ℝ)‖ < _ at hs
       rw [← mul_sub,← Int.cast_sub,Real.norm_eq_abs,abs_lt] at hs
       rw [Schedule.radius, ← C.S.span_side N p] at hs
       have hk : (-(C.side N p).val:ℝ) < 2*↑(d i) ∧ (2:ℝ)*↑(d i) < (C.side N p).val := by
          change -((C.S.side N p).val : ℝ) < _ ∧ _ < ((C.S.side N p).val:ℝ)
          change -_ < C.S.a N*↑(d i) ∧ C.S.a N*↑(d i) < _ at hs
          constructor
          · apply lt_of_mul_lt_mul_left (a:= C.S.a N) _ hp.le
            linarith only [hs.1]
          apply lt_of_mul_lt_mul_left (a:= C.S.a N) _ hp.le; linarith only [hs.2]
       refine ⟨?_,?_⟩
       · exact_mod_cast hk.1
       exact_mod_cast hk.2.le
    rw [Schedule.place,hz]; apply PiLp.ext; intro i; simp only [Schedule.place,Schedule.gridPoint, PiLp.sub_apply,WithLp.ofLp_toLp,d,Pi.sub_apply,Int.cast_sub]; ring

lemma nativeShort {x y: Site (C.side N p)}(h:‖C.S.place x-C.S.place y‖ < C.S.radius p):
  C.S.a N * separation x y ≤ ‖C.S.place x-C.S.place y‖ ∧ ‖C.S.place x-C.S.place y‖ ≤ 2*C.S.a N*separation x y:=by
     rw [← shortWay C h]; simpa only [separation, sub_zero] using MergeProof.Ribbons.normC C N p (x-y)

variable (F:Final C f S)(T: Test 1)(K:Set (Points (n+1)))

/-- Absolute stencil admitted by chart, retaining full mask for actual values. -/
def gathersIn (_:Final C f S)(T: Test 1)(K:Set (Points n))(r:ℝ) : Set (Points n):=
    absCord n 0 r '' (K ×ˢ tsupport T)

theorem gathered {ψ: Test (n+1)}{r:ℝ}(hp:IsCompact K)(hh:tsupport ψ ⊆ K) : tsupport (shape (cashier F T) r ψ)⊆ gathersIn C F T K r:=by
   by_cases hk : r≠0 ∧ packs (cashier F T) r ψ
   · rw [shaped (cashier F T) hk.1 hk.2]; exact absolute_lands (cashier F T) hp hh hk.1
   unfold shape; rw [dif_neg hk]; change tsupport (0:Points (n+1)→ℂ) ⊆_; simp

theorem stencilSpace (hp:IsCompact K) (hh:K⊆conf _) : ∃ μ υ η:ℝ,0 ≤ μ ∧ 0<υ ∧ 0<η ∧
    ∀ᶠ r in home,∀ N p:ℕ,∀ u: Fin (n+1)→Site (C.side N p),Extraction.Order.cells C N p u ∈ gathersIn C F T K r →
      (∀ i,‖C.S.place (u i)‖ ≤ μ) ∧
        (∀ i j,C.S.a N*separation (u i) (u j) ≤ υ*r) ∧
          (∀ i j,i≠j → η*r ≤ 2*C.S.a N*separation (u i) (u j)):=by
    obtain ⟨R,δ,hR,hδ,hK⟩:=roomCosts hp hh
    obtain ⟨B,hB⟩:= T.hasCompactSupport.exists_bound_of_continuousOn (f:=Prod.fst ∘ (openRoot (k:=0)).symm) (continuous_fst.comp openRoot.symm.continuous).continuousOn
    let υ:=2*R+1
    have hy:0<υ:=by unfold υ; linarith
    refine ⟨R+max B 0,υ,δ, add_nonneg hR (le_max_right ..),hy,hδ,?_⟩
    have hx : ∀ᶠ r in home, r < (1/2)/υ := nhdsWithin_le_nhds (gt_mem_nhds (by positivity))
    filter_upwards [positiveLength,(show ∀ᶠ r in home,r ≤ 1 from nhdsWithin_le_nhds (ge_mem_nhds (zero_lt_one))),hx] with r hr hr' hz N p u hp
    obtain ⟨⟨x,z⟩,hh',he⟩:=hp; obtain ⟨⟨o,v⟩,rfl⟩:=openRoot.surjective z
    have he(i:Fin (n+1)) : C.S.place (u i)=posed r x i + o:=by
       have hg:=congr_arg (fun (p: Points (n+1+0))=> p.ofLp (Fin.castAdd 0 i)) he
       simp only [absCord,ContinuousLinearEquiv.symm_apply_apply,pad_xy,Extraction.Order.cells,points,WithLp.ofLp_toLp,Fin.append_left] at hg; exact hg.symm
    obtain ⟨hT,hw⟩:= hK r hr x hh'.1
    have hZ: ‖o‖≤B:=by simpa only [Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using hB _ hh'.2
    simp only [sub_zero] at hT; have hb:= le_max_left B 0
    have hi(i j:Fin (n+1)):‖C.S.place (u i)-C.S.place (u j)‖ ≤ υ*r:=by
       rw [he,he,add_sub_add_right_eq_sub]; refine (norm_sub_le ..).trans ?_; unfold υ; linarith [hT i,hT j]
    have hs(i j:Fin (n+1)):= nativeShort C (x:=u i) (y:=u j) (by
       refine lt_of_le_of_lt (hi i j) (lt_of_lt_of_le ?_ (show (1/2:ℝ) ≤ C.S.radius p from div_le_div_of_nonneg_right (mod_cast (C.S.period p).property) (by norm_num)))
       rw [mul_comm]; exact (lt_div_iff₀ hy).mp hz)
    refine ⟨fun i=> ?_,fun i j=> (hs i j).1.trans (hi i j),fun i j h=>?_⟩
    · rw [he]; exact (norm_add_le ..).trans (add_le_add ((hT _).trans (mul_le_of_le_one_right hR hr')) (hZ.trans hb))
    refine le_trans ?_ (hs i j).2; rw [he,he,add_sub_add_right_eq_sub]; exact hw i j h
end YM.RG17
