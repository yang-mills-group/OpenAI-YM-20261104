import YM.MS.Vista.Plain
/-!
# Geometry scales.Window machine. λ warp initially 1. Flank clamps after gate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}{P:Belt I}
-- cost.Assumption no temporal parameter.X≥1 fixed.
structure Visa (I:Type) where
    bank : I→ℝ
    here : ∀ i,1≤ bank i
abbrev tickA (L:I→Side)(i:I): ℝ := (dimT L i).val
abbrev until0 (L:I→Side)(i:I):= Real.log (1+ tickA L i)
lemma δ_L (L:I→Side)(i:I): 1≤tickA L i:= by exact_mod_cast PNat.pos ( dimT L i ) -- lt.
lemma δ_p (L:I→Side)(i:I): 0<tickA L i:= lt_of_lt_of_le zero_lt_one ( δ_L L i )
lemma φ_day (L:I→Side)(i:I): 0≤until0 L i:= Real.log_nonneg (by obtain h:= δ_p L i; linarith)
lemma τ_h (L:I→ Side)(i:I): τ (until0 L i)= tickA L i:= by unfold until0 Vista.τ; rw [Real.exp_log]; ring; obtain h:=δ_p L i; linarith
lemma glowH (L:I→Side)(i:I): lamp (until0 L i)=tickA L i:= by rw [ Vista.lamp, τ_h,max_eq_right (δ_L ..) ]
abbrev wallet (M:Visa I)(i:I)(t:ℝ):= M.bank i*(1+|t|)
def Rich (M:Visa I)(Λ: I→ Set ℝ)(H:∀ i,MeasurableSet (Λ i))(p:Moments I ℝ)(hp:∀ i t,t∈ Λ i→0< p i t): Belt I:= ⟨ Λ,⟨ fun t=>p t.1 t.2,fun t=>hp t.1 _ t.2.property,fun t=> wallet M t.1 t.2,fun i=> one_le_mul_of_one_le_of_one_le ( M.here _ ) ( by simp ) ⟩, H ⟩
lemma lamp_l (x:ℝ): 1≤lamp x:=le_max_left ..
lemma lamp_p(x:ℝ): 0<lamp x:= lt_of_lt_of_le zero_lt_one (lamp_l x)
abbrev unbounded (M: Visa I):= Rich M (fun _=>Set.Ici 0) (fun _=>measurableSet_Ici) (fun _=>lamp) (fun _ t _=>lamp_p t)
abbrev midpoint (M:Visa I)(L:I→Side):= Rich M (fun i=> Set.Icc 0 (until0 L i)) (fun _=>measurableSet_Icc) (fun _=> lamp) (fun _ t _=>lamp_p t)
abbrev After (M:Visa I)(L:I→Side):= Rich M (fun i=>Set.Ici (until0 L i)) (fun _=>measurableSet_Ici) (fun i _ => tickA L i) (fun i _ _=> δ_p L i)
lemma τ_m : Monotone τ:= fun _ _ he=> sub_le_sub_right ( exp_monotone he) _
lemma lamp_m : Monotone lamp := fun _ _ he=> max_le_max le_rfl (τ_m he)
-- Town∎
variable {M:Visa I}{L:I→Side}{k a b:ℕ}
structure Market (P:Belt I)(M:Visa I)(a:I→ℝ): Prop where
   acc : Accel P a
   begin_nn i:0≤ a i
   large i:1≤ P.price.length i
   fund i:P.price.basic i=wallet M i.1 (tstart i)
lemma buildM (s:I→Set ℝ)(F:Moments I ℝ)(J:∀ i,MeasurableSet (s i))(he:∀ i t,t∈s i→1≤ F i t)(hp:∀ i, Monotone (F i))(v:I→ℝ)(ho:∀ i,v i∈s i)(hv:∀ i,s i∩ Set.Iic (v i)={v i})(hn:∀ i,0≤v i)(hc:∀ i,OrdConnected (s i)): Market (Rich M s J F (fun i t h=> lt_of_lt_of_le zero_lt_one (he i t h))) M v:= by
   let P:=Rich M s J F (fun i t h=> lt_of_lt_of_le zero_lt_one (he i t h)); change Market P M v; have hH(i t) (hp:t∈s i):v i≤t:= by apply le_of_not_gt; intro hx; have he:t∈( {v i}:Set ℝ ):= hv i ▸ ⟨ hp,hx.le⟩; exact hx.ne he
   have heq(p:P.time):v p.1 ≤ tstart p:= hH _ _ p.2.property; have hx (p:P.time):0≤ tstart p:= le_trans ( hn _ ) (heq p); have hB(i:I): 1≤ M.bank i:=M.here i; have hnQ(x:P.time):P.price.basic x= M.bank x.1 * (1+ tstart x):= by change _*(1+|tstart x|)=_; rw [abs_of_nonneg (hx x)];
   refine ⟨ ⟨ ho,?_,fun x=>?_,?_,?_⟩,hn,fun x=> he _ _ x.2.property,fun _=> rfl ⟩; swap
   · obtain hm:= M.here x.1; rw [hnQ]; nlinarith [hx x, hn x.1]
   · intro p; ext x; constructor; · intro hz; exact ⟨ hc p.1 |>.out' ( ho _ ) p.2.property hz, hz.2 ⟩ -- name
     exact fun h=> ⟨ hH _ x h.1,h.2 ⟩
   · intro x y hz hv; rw [hnQ,hnQ,hz]; gcongr; exact (zero_le_one.trans ( hB _ ))
   intro x y hx ht; change F x.1 (tstart x)≤ F y.1 (tstart y); rw [hx]; exact hp _ ht
lemma ici_eq (t:ℝ): Set.Ici t∩ Set.Iic t={t}:= by ext i; simp; exact ⟨fun h=> h.1.antisymm h.2|>.symm,fun h=> ⟨ h.ge,h.le⟩⟩
lemma ontoM : Market (unbounded M) M 0:= buildM _ _ _ (fun _ t _=> lamp_l t) (fun _=>lamp_m) _ (fun _=>Set.mem_Ici.mpr le_rfl) (fun _=> ici_eq 0) (fun _=>le_rfl) (fun _=> ordConnected_Ici)
lemma nextM : Market (midpoint M L) M 0:= by
    refine buildM _ _ _ (fun i t _=> lamp_l _) (fun _=>lamp_m) _ (fun i=> ⟨le_rfl,φ_day _ _⟩) ?_ (fun _=>le_rfl) (fun _=> ordConnected_Icc)
    intro i; change Set.Icc 0 (until0 L i)∩ Set.Iic 0=_; ext q; simp; obtain h:=φ_day L i; constructor <;> grind
lemma soonM : Market (After M L) M (until0 L):= buildM _ _ _ (fun i _ _=> δ_L L i ) (fun _=>monotone_const) _ ( fun _=> Set.mem_Ici.mpr le_rfl ) (fun _=> ici_eq _ ) ( φ_day L ) ( fun _=>ordConnected_Ici )
-- scale endpoint tasks shown next
end YM.MS.Vista
