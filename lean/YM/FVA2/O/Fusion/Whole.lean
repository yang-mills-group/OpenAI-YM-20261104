import YM.FVA2.O.Product.Land
/-!
# Ranks to determine propagation inherited property
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Serve
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff
open scoped Topology ContDiff
variable {G:Gauge}{t:Bool}{O:Type}{I:Type}{U:Planet G I}{F H:Glade G I}{B: Deck G}{K:Booked B}{M:MS_Data G K}{q:ℤ}{r n:ℕ}{x:Law G}
local notation "A"=> both G I
abbrev disc (F:Glade G I)(r:ℕ): Glade G I := fun i t=> Book.mask r ( F i t )
lemma disc_eq (v:List (Lane4 G)) (x:Law G) : Book.mask r x v= if v.length=r then x v else 0:= by by_cases hx:v.length=r; rw [ enough _ (by omega),if_pos hx ]; rw [ strange _ (by omega),if_neg hx ]
lemma embrace (h:Warm F false): Warm ( disc F r ) false:= by
    refine ⟨ fun i t ht=> stepOver ( pinch ( h.cost i t ht ) (fun z=>Bool.noConfusion z) ) (fun _=>zero_le_one),fun i w _=>?_⟩; simp_rw [disc,disc_eq]; by_cases he:w.length=r; simp_rw [if_pos he]; exact h.walk _ _ (fun z=>Bool.noConfusion z); simp_rw [if_neg he]; exact continuous_const
lemma silent (F:Law G)(u:G.El): repeatC u ( mask r F )=mask r ( repeatC u F ) := by
    funext l; by_cases ht:l.length=r; · rw [enough _ (by omega)]; exact High.paint_congr _ _ (fun w hw=> enough _ (by rw [High.paint_len _ _ hw]; omega))
    rw [strange _ (by omega)]; exact High.paint_zero _ _ (fun w hw=> strange _ (by rw [High.paint_len _ _ hw]; omega))
lemma plank (hp:Solid false x q): Solid false (mask r x) q := by
    constructor; · intro l i j k hl; simp_rw [disc_eq]; rw [ hp.symm _ _ _ _ hl ]; simp only [ List.length_append,List.length_cons ]; split <;> (first | rfl | exact ( mul_zero _ ).symm )
    · intro l hl hk; simp_rw [disc_eq,hp.ghost _ hl hk]; simp
    · intro w _ u; change repeatC u (Book.mask r x) _=_; rw [silent,Ward.ink hp]
    intro w hw; simp_rw [disc_eq,hp.real' _ hw,invertMom,List.length_map]; split <;> simp
lemma collate (h: ∀ r:ℕ,Solid false (mask r x) q): Solid false x q:= by
    constructor; · intro l i j k hl; obtain he:= h (l.length+k.length+2) |>.symm l i j k hl; rw [enough _ (by simp; omega),enough _ (by simp; omega)] at he; exact he
    · intro l hl hx; rw [← (enough (F:=x) (h:=(l.length:ℤ)) l rfl) ]; exact ( h l.length ).ghost l hl hx
    · intro w _ u; obtain he:= Ward.ink (h w.length) u; rw [silent] at he; obtain ht:= congr_fun he w; rw [enough _ rfl,enough _ rfl] at ht; exact ht
    intro w hw; obtain he:=(h w.length).real' _ hw; rw [enough _ (by simp [invertMom]),enough _ rfl] at he; exact he
-- Warm orbit projection. Need map chains
lemma plateC (h:Warm F false): disc ((both G I).P (disc F (r+2))) r=disc ((both G I).P F) r:= by
    rw [ show (both G I).P (disc F (r+2)) = _ from spine ( embrace h ) realityA, show (both G I).P F=_ from spine h realityA ]; funext i t w; simp_rw [disc,disc_eq]; -- simp trap disc rewrites inner, but cycle_mask?
    split; rename_i e; exact (cycle_mask _ _ e).symm; rfl
lemma intSolid {E:Type}[MeasurableSpace E]{F:E→Law G}(ν:Measure E)(hp:∀ w,Integrable (fun i=> F i w) ν)(hv:∀ i,Solid false (F i) q): Solid false (fun w=> ∫ i,F i w ∂ν) q := by
    constructor; · intro l i j k hl; simp_rw [(hv _).symm l i j k hl,integral_const_mul ]
    · intro l hl hm; simp_rw [ (hv _).ghost l hl hm ]; exact integral_zero _ _
    · intro l hl v; change repeatC v ( fun w=>∫ i, F i w∂ν ) l=_; rw [MS.Color.rep_integral (j:=v) (μ:=ν) hp l]; simp_rw [ Ward.ink (hv _) v ]; -- no extra
    intro w hw; simp_rw [ (hv _).real' w hw ]; exact integral_conj
-- generic recursive solution for multi. Using Trip w linear extension but motion with no net restriction.
lemma triple (h: Warm F false)(he: Bank H q)(hx: Trip (fun v=> (both G I).P v) F H): Bank F q := by
    refine ⟨ h,hx.1,?_⟩; intro i t; obtain ⟨M,hM⟩:= hx.1; let S(i':ℕ):Prop:= ∀ i:I,∀ v:ℝ,Solid false (disc F i' i v) q; refine collate (x:=F i t) (fun r=>?_); -- F named x
    have hz (r:ℕ)(hr:M<r): S r:= by
        intro i t; rw [show disc F r i t=0 from funext fun w=> (by unfold disc; rw [disc_eq]; split; rename_i e; exact hM i t w (by omega); rfl) ]; exact solid_zero
    suffices Hs : ∀ (v:ℕ) (r:ℕ), M ≤ v+r → S r from Hs M r (by omega) i t
    intro v; induction v using Nat.strong_induction_on with
    | h k IH=>
       intro r hr; by_cases hp:M<r; exact hz r hp
       intro i t; have hu:S (r+2):= by by_cases h:M<r+2; exact hz (r+2) h; exact IH (k-1) (by omega) (r+2) (by omega)
       let X:=(both G I).P F + H; rw [ show disc F r i t=fun w=> ∫ s in Set.Iic t, disc X r i s w from funext ( fun w=>?_ ) ]; swap; · unfold disc; simp_rw [disc_eq]; by_cases he:w.length=r; simp_rw [if_pos he]; exact congr_fun (congr_fun (congr_fun hx.2.2 i) t) w; simp_rw [if_neg he]; simp
       apply intSolid _; · intro w; unfold disc; simp_rw [disc_eq]; split_ifs with he; exact hx.2.1 i t w (fun x=>Bool.noConfusion x); simp
       intro v; unfold X disc; change Solid false (mask (r:ℤ) ( (both G I).P F i v+ H i v )) q; rw [map_add]; let S:= hu i v; rw [show mask _ ((both G I).P F i v)=_ from congr_fun (congr_fun (plateC (r:=r) h).symm i) v]; exact ( plank ( sA S ( Wallet.awake ( embrace h ) i v ) ) ).add ( plank ( he.tone i v ) )
end YM.FVA2.O.Serve
