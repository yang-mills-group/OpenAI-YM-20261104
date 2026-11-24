import YM.FVA2.Rank.Cap
import YM.FVA2.Rank.Sky
/-!
# Helpers to recognize parity of any Team in the computed prescriptions

`cancel` helps rule out misplaced terms. Needed to learn that no inadmissible
power of $g$ is used in tuning at a finite regulator. Not an assumption relating two MS schemes. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hue.Agent.Signal
open Function Filter Set Finset Lattice MeasureTheory Real
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Native MS.Native.Wilsonian MS.Book MS.Book.Program MS.Book.Convolve MS.Dock MS.Train MS.Pearl MS.Emit
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Menus MS.City
open MS.Outlook MS.LogTime MS.LogTime.IntervalFamily MS.Plane.Wire MS.Plane.Domain MS.High.Knobs MS.Motif MS.Land
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{p q:Team}{k m i a:ℕ}{v:ℤ}{b:Bool}
-- opening Heat.Signal namespace conflicts Hue.Agent.Signal
variable {F H: Recount G} (x:ℝ) (w:List (Lane4 G))
section
variable (R:Trust b v (F i) (H i) k) (hall:Course b w)(hW:w.length=k)(ha:fieldDim wfield w+a≤v)
local notation "Ω"=> (ray w)
include R hall hW ha
lemma fade : Origin (F i-H i) Ω a x 0:= by
    have hL:= R ℝ Ω (ray_course hall) (by rw [ray_len,hW]); have ht := to_price hL;
    obtain ⟨C,hC,i',hi⟩:= ht.quoted a; unfold Origin; let D:= ((↑(fieldDim wfield Ω-v):ℝ)-eps_gain); let L:= D+(a:ℝ); have hZ : L<0 := (int_need p_gain s_gain).mpr (by rw [ray_dim]; omega );
    apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero' (g:=fun t=> C* meet.logPart x ^ i' * LogTime.polyExp (-L) i' t ); · exact Eventually.of_forall fun _=> norm_nonneg _
    · filter_upwards [ eventually_ge_atTop ( meet.beg x ) ] with t h
      let u:= meet.choose x t h; specialize hi u 0 (Set.mem_univ _); apply hi.trans (le_of_eq ?_); change C*( meet.logPart x * (1+t) * (1+exp t* ‖(0:ℝ)‖ )) ^ i' * ( (1*exp ( D*t )) * exp t ^ a)= _; simp only [ polyExp, norm_zero, mul_zero, add_zero,mul_one,one_mul,neg_neg,L,mul_pow,add_mul, Real.exp_add,Real.exp_nat_mul ]; ring
    simpa using (LogTime.vanishes (b:= -L) (neg_pos.mpr hZ) i').const_mul (C * meet.logPart x ^ i')
lemma fade_v (he:∀ t,ContDiff ℝ ∞ (fieldVal ((F i-H i) (x,t)) (ray w))) : Tendsto (fun t=> torch a ((F i-H i) (x,t)) w) atTop (𝓝 0):= by simpa only [ray_sail] using (origin_ray_iff ⟨_,fade x w R hall hW ha⟩ he).mp ( fade x w R hall hW ha ) 1
end
variable {xh: ℝ×ℝ}
lemma erase (h:w.length%2≠i%2)(hk:Hue.only i (F i xh)) : fieldVal (F i xh) (ray w)=0:= by
    funext x; exact hk _ (by rw [sail_len,ray_len]; exact Ne.symm h)
variable {s:ℝ→Law G} {X:T ( Flats G )} {Y:T (Coat G)} (h:G.Simple) (hM:leader G X (gloss (pulseX G)) Y)
variable (hp:1≤ i )(ht: Fixed ( col ( skyline G p ) ) ( Archive 4 X ) true 4 1 )
   (hc:Career G p q i k 4 s)(hne: k%2≠i%2) (hz:Wage i q)
local notation "O"=> Archive 4 X
local notation "Σ₀"=> col (skyline G p)
local notation "Σ₁"=> col (skyline G q)
include h hM hp ht hc hne hz
lemma cancel (he:Course true w)(hl:w.length=k)(hP:fieldDim wfield w+a=(4:ℤ))(h0:0<k): s x w=0 := by
    let M:= Σ₀ i-O i; have hke: Course true (ray w):= ray_course he; have ht': MS.High.Disc true 1 O O _ 4 := MS.Outlook.dock hM wisdom; have hu: (ray w).length=k:= by rwa [ray_len];
    have hU: Used true (ray w):= fun h=> hu.symm ▸ h0
    have hT(t:ℝ):ContDiff ℝ ∞ (fieldVal (O i (x,t)) (ray w)):= ((ht'.master.road ℝ _ _ hp hU) hke).1 _;
    have ho(t:ℝ): ContDiff ℝ ∞ (fieldVal (Σ₀ i (x,t)) (ray w)):= (( SatSolve h (skyPC G p)|>.road ℝ _ _ hp hU) hke).1 _
    apply tendsto_nhds_unique _ (fade_v (F:= Σ₀ ) (H:=O) x w (ht i hp k (fun _=>h0)) he hl hP.le (fun t=> ( ho t ).sub (hT t))); -- rewrite function equals constant
    let N t:= torch a ( ( Σ₀ i-O i ) (x,t) ) w; have ha : ∀ t,N t = s x w:= by
       intro t; unfold N; rw [Pi.sub_apply, torch_sub w (ho t) (hT t) ]; have h3:w.length%2≠i%2:= by rw [hl]; exact hne
       have hE(f:Recount G)(hk:Hue.only i (f i (x,t))):torch a (f i (x,t)) w=0:= by rw [torch_at]; change reading a (fieldVal (f i _) _)=0; rw [erase _ h3 hk]; simp [reading] -- need simp
       rw [ hE _ ( Position.Glazer.gone hM i (x,t)),sub_zero ]; obtain hv:= bulk_pay (skyPC G p) (skyPC G q) hc hp; have ha': Move true ( Key G ) p q i k 4 s := rewind (hp:=p) (hq:=q) (K:=Key G) rfl rfl hc.past (fun j=> ((skyPC G p).owes i |>.stay j).joint) (fun j=> ((skyPC G q).owes i |>.stay j).joint) hv
       have hm : torch a (Σ₁ i (x,t)) w= torch a (Σ₀ i (x,t)) w - ( if fieldDim wfield w + a=4 then s x w else 0) := ha'.tune x t _ he hl a hP.le; rw [ hE _ ( TrueSky hz G (le_refl i) _ ), if_pos hP ] at hm; exact sub_eq_zero.mp hm.symm
    exact (show Tendsto (fun t:ℝ=> s x w) atTop (𝓝 (s x w)) from tendsto_const_nhds).congr (fun x=> (ha x).symm)
end YM.FVA2.Hue.Agent.Signal
