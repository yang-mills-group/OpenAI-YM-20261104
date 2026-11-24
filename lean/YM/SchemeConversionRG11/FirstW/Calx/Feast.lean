import YM.SchemeConversionRG11.FirstW.Calx.Flood
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{T:Itinerary}{c:ℕ→Side}
structure Aura (T:Itinerary)(r R: ℝ)(f:ℕ → Cover→ ℝ): Prop where
 ends : Lives T R f
 front: ∀ᶠ i in atTop,∀ x:Cover,Jam T r i x → f i x=0
lemma march_shell (Q:Wash)(p:ℕ→Field4 G)(w:Walk)(T:Itinerary)(r:ℝ)(h:r<Q.rIn)(R:ℝ)(hR:Q.rOut<R) : ∀ᶠ i in atTop,∀ x:Cover,(Jam T r i x ∨ ¬ Jam T R i x) → scar Q T w p i x=0 := by
 -- every cost leg vanishes through mask plateau first
 have ht(y:Cover): ∀ᶠ i in atTop,∀ x:Cover,(Jam T r i x ∨ ¬ Jam T R i x) → tabL T Q i (x+y)=tabL T Q i x := by
    filter_upwards [birthM (T:=T) h y,birthM (T:=T) hR (-y)] with i hi hx x he
    rcases he with h'|hr
    · rw [tabL,tabL,soft_clear Q _ (hi x h'),soft_clear Q _ (le_trans h' h.le)]
    have hp : ¬ Jam T Q.rOut i (x+y) := fun v=> hr (by simpa using hx _ v)
    rw [tabL,tabL,soft_life Q _ (lt_of_not_ge hp).le,soft_life Q _ (by exact hR.le.trans (lt_of_not_ge hr).le)]
 have he (y:Cover) :∀ᶠ i in atTop,∀ x:Cover,(Jam T r i x ∨ ¬ Jam T R i x) → rail (x+y) w (windM T Q i (p i))=tabL T Q i x • rail (x+y) w (p i):= by
   induction w generalizing y with
   | nil=> simp only [rail,LinearMap.zero_apply,smul_zero]; simp
   | cons a w ih=>
     filter_upwards [ih (y+a.vec), ht (y+torMark a)] with i hi hq x hx
     rw [rail,LinearMap.add_apply,LinearMap.add_apply,smul_add,add_assoc,hi x hx,scar_value, hq x hx]
 refine (he 0).mono fun i hi x h=>?_; unfold scar; apply sub_eq_zero.mpr; simpa only [add_zero,tabL] using hi x h
-- integrands by ticket
abbrev oweX (T:Itinerary)(Q:Wash)(a b:Who G 6)(ε: Cover→G.Color)(u v:Ticket)(m:ℕ)(x:Cover):= let F:=icon (fresh u) (fresh v); inner ℝ (rail x F (tin G (T.period m) a)) (scar Q T F (fun i=> shiftT ε (tin G (T.period i) b)) m x)
lemma oweX_pay (T:Itinerary)(Q:Wash)(l:ℕ)(a b:Who G 6)(ha:fee a=2)(hb:fee b=2)(ε: Cover→G.Color)(he:ε∈Loft _ (l+1))(u v:Ticket): Melody T {x:E4|x≠0} ((l:ℤ)-7) (oweX T Q a b ε u v):=by
 let p:=icon (fresh u) (fresh v)
 have hp:= Melody.linked (rail_m (fresh u) (fresh v) (lit_point a T ha)) (scar_lands Q p (fun s=>smock_step (l+1) _ (lit_point b T hb).cap ε he s)) (innerSL ℝ (E:=G.Color))
 have h:(l:ℤ)-7=(-3:ℤ)-1+(-3+ ((l+1:ℕ):ℤ)-1):=by omega
 rw [h]; exact hp
lemma glow_done {f:ℕ → Cover→ ℝ}{r R:ℝ}{k:ℤ}(he:r>0)(hR:R>0)(h:Aura T r R f)(hp: Melody T {x:E4|x≠0} k f)(hc:MarkGrid T c) : Helen (fun i=> T.gap i^(4+k) * expenditure T f i):= by
 obtain ⟨g,hg⟩:= hp; let p:=ped T k f
 let S:= closedBall (0:E4) R \ ball (0:E4) r
 have hx:IsCompact S:= (isCompact_closedBall ..).diff isOpen_ball
 have hk:S ⊆ {x:E4|x≠0}:= fun i hi ht=>hi.2 (ht.symm ▸ mem_ball_self he)
 obtain ⟨C,hC,H⟩:= hg.rent hx hk
 have hj : Lives T R p:= Eventually.mono h.ends (fun i hi x hx=> hi _ (fun h=>hx (by simp [p,h])))
 have hh:NearCost T p := by
    refine ⟨(R+1)^3*C,by positivity,?_⟩
    filter_upwards [H, h.front,hj,T.cutoff.eventually (ge_mem_nhds (show (0:ℝ)<1 from one_pos))] with i hi hl hj ht x
    have hv:= T.positive i; have hf:0≤ Foot T i x := (mul_pos hv (zero_lt_one.trans_le (unit_stepY _))).le
    by_cases hy:p i x=0; · rw [hy,norm_zero,mul_zero]; positivity
    have Ht: Jam T R i x := hj x hy; have Hp : ¬ Jam T r i x:= fun m=>hy (show p i x=0 from by simp [p,hl x m]); exact mul_le_mul (pow_le_pow_left₀ hf ((limb Ht).trans (by linarith)) 3) (hi x ⟨mem_closedBall_zero_iff.mpr Ht,fun z=>Hp (show ‖Moss T i x‖≤r from (mem_ball_zero_iff.mp z).le)⟩) (norm_nonneg _) (by positivity)
 have he (x:E4) (hp:x≠0)(o:ℕ → Cover)(h:Harbor T o x): Tendsto (fun i=>p i (o i)) atTop (𝓝 (g x)):= hg id tendsto_id x hp o h
 refine ⟨_, (mount hj hc hh he).2.congr fun i=>?_⟩; dsimp only [p,ped]; unfold expenditure; simp only [smul_eq_mul,← Finset.mul_sum,zpow_add₀ (T.positive i).ne', zpow_ofNat]; ring
lemma here_bill (Q:Wash)(l:ℕ)(ε:Cover→ G.Color)(hε:ε∈Loft _ (l+1))(a b:Who G 6)(ha:fee a=2)(hb:fee b=2)(hc:MarkGrid T c) (u v:Ticket): Helen (fun i=> T.gap i^((l:ℤ)-3)* expenditure T (oweX T Q a b ε u v) i):=by
 have hj : Q.rIn>0:=Q.rIn_pos
 have hk:=march_shell Q (fun i=>shiftT ε (tin G (T.period i) b)) (icon (fresh u) (fresh v)) T (Q.rIn/2) (by linarith only [hj]) (Q.rOut+1) (lt_add_one _)
 have hp : Aura T (Q.rIn/2) (Q.rOut+1) (oweX T Q a b ε u v):= ⟨hk.mono (fun i hi x h=>by by_contra! hv; unfold oweX at h;simp [hi x (Or.inr hv)] at h), hk.mono fun i hi x H=>by simp [oweX,hi x (Or.inl H)]⟩
 rw [show (l:ℤ)-3=4+(l-7) by omega]; exact glow_done (by linarith only [hj]) (by linarith only [Q.rOut_pos]) hp (oweX_pay _ _ _ _ _ ha hb _ hε u v) hc
end YM.RG11.FirstW
