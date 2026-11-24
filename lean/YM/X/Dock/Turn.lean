import YM.X.Dock.Yield
/-!
# map explicit derivative off diagonals and hold visae.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Dock
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset MeasureTheory Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Imprint CellsInt Beamer Asymptotics
open Maxwell (Green normal grad)
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k d:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ} {A B:Scaff}
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
lemma air_moves (h:A∈air d) (w x y:Site n) : A n (x+w) (y+w)=A n x y:= by rw [air_span] at h; induction h using Submodule.span_induction with|zero=>rfl|mem A hv=>obtain ⟨l,x,h,rfl⟩:=hv; simp only [graphS,add_sub_add_right_eq_sub]; | add A B _ _ hi hj=>exact congr_arg₂ (· + ·) hi hj| smul c A _ hi=> exact congr_arg (fun v:ℝ=> c * v) hi -- section mistake
abbrev run (q:ℕ+)(X:Fielding.Walk)(d:ℕ)(A:Scaff):Rhyme q:= fun k=>sprite (epsilon q k) d A (side q k) (transit q X k)
abbrev pin (q:ℕ+)(X:Fielding.Walk)(U:Rhyme q): Mist ℝ:= fun k z=> U k (transit q X k+wrap _ z)
structure Atlas (q:ℕ+)(d:ℕ)(A:Scaff)(φ:E4→ℝ) : Prop where
   mark : A∈ air d
   edge {X Y:Fielding.Walk}{x y:E4}(hx:plot q X x)(hy:plot q Y y)(h:x≠y):Tendsto (cable q X Y d A) atTop (𝓝 (φ (x-y)))
variable (hq:1<q.val) {φ γ:E4→ℝ}
local notation "ω" X:arg d:arg A:arg=> pin q X (run q X d A)
include hq
lemma within (h:A∈air d)(X:Fielding.Walk)(hr:R≥0): Visa q R (-((2+d:ℕ):ℤ)) (-((2+d:ℕ):ℤ)) (ω X d A):=by
    have ht:= Visa.asPow (c:=-((2+d:ℕ):ℤ)) (rooted_bird hq hr (sky.mp h)); rw [add_zero] at ht; refine cast (congr_arg (Visa q R (-((2+d:ℕ):ℤ)) (-((2+d:ℕ):ℤ))) ?_) ht; ext1 k; ext1 z; let u:= transit q X k; let v:= wrap (side q k) z; unfold pin run; rw [zpow_neg,zpow_natCast, sprite_val,smul_eq_mul]; congr 1; unfold castG; simp only [LinearMap.coe_mk,AddHom.coe_mk,map_zero]; simpa only [zero_add,add_comm v u] using (air_moves h u 0 v).symm
variable (S:Finset V)(P:V→Fielding.Walk)(p:V→ E4)(χ:Floor R)(H: Apart S p R)(hp:∀ i∈S,plot q (P i) (p i))
include H hp
lemma barometer {i:V}(hi:i∈ S)(h:A∈air d): Isle q S P p χ (2+d) (castV (run q (P i) d A)):= by
    let u:= P i; obtain ⟨C,hC,h⟩:= Print.cost hq (sky.mp h); obtain ⟨c,hc,ht⟩:= fare hq S P p hp χ H hi; let m:=2+d; refine ⟨⟨C*c^m,by positivity,?_⟩,fun {v} hv z hz=>?_ ⟩; swap; · apply Released.lin Complex.ofRealCLM.toLinearMap; exact floated hq (fun e=>hv ⟨i,hi,e⟩) (hp i hi) hz A (by assumption) -- lin domain
    filter_upwards [h,ht] with j hj hh z hz he; let t:= ε j; let n:=side q j; let v:= wrap n z; let w:= transit q u j; let r:=Interval.mass v w; let a:= A n w v; specialize hj (u j) z; unfold Print.scale at hj; rw [comm] at hj; have ht: 0<t:= epsilon_pos ..; have hy: Width q j z>0:= zero_lt_one.trans_le (depth ..); unfold castV run; rw [sprite_val,inv_mul_eq_div,Complex.norm_real,norm_div,norm_pow]; change ‖a‖ / ‖t‖^m * _ ≤ _;rw [Real.norm_of_nonneg ht.le]
    calc _ ≤ ‖a‖ / t^m * (c*(t*r))^m:= by gcongr; apply hh z hz he
         _ = ‖a‖*r^m*c^m:= by rw [mul_pow,mul_pow]; field_simp
         _ ≤ _ := by gcongr; exact hj
omit H hp hq
lemma gone {x w z:E4}(h: R< ‖x-w‖)(hr: ‖z‖ ≤ R) : x≠w+z := fun e=> by rw [e,add_sub_cancel_left] at h; exact not_lt_of_ge hr h -- w+z-w
lemma street_point (h:Atlas q d A φ){X Y W: Fielding.Walk}{x y w:E4}(hx:plot q X x)(hy:plot q Y y)(hw:plot q W w)(hp:x≠y+w):Tendsto (fun k=> pin q Y (run q X d A) k (W k)) L (𝓝 (φ (x-(y+w)))):= (h.edge hx (hy.add hw) hp).congr fun k=> by unfold cable transit pin run; rw [Pi.add_apply,map_add]
variable {X Y:Fielding.Walk}{x y:E4}(hx:plot q X x)(hy:plot q Y y)
include hx hy hq
lemma outside (h:Atlas q d A φ)(hr:R≥0)(H:R < ‖x-y‖): Visa q R 0 0 (pin q Y (run q X d A)):= by
    obtain ⟨C,hC,hv⟩:= Print.cost hq (sky.mp h.mark); obtain ⟨a,ha,he⟩:= Fielding.gate_far hq R hr H (plot.sub hx hy); let d':=2+d; let U:=X-Y; refine ⟨⟨C/a^d',by positivity,?_⟩,fun p hp hr z hz=>?_⟩; swap; · simp only [sub_zero,zpow_zero,one_smul]; exact ⟨_,street_point h hx hy hz (gone H hr)⟩
    filter_upwards [he,hv] with i hi hj z hz; specialize hi z hz; specialize hj (U i) z; let t:= ε i; let n:=side q i; let u:= wrap n (U i); let v:=wrap n z; let r:=Interval.mass u v; have ht: t>0:=epsilon_pos ..; have hr: 0<r:= pay_pos u v; rw [comm] at hi; have he : castG A n (U i) z=A n (transit q X i) (transit q Y i+v):= by
        change A n u v=_; rw [← air_moves h.mark (transit q Y i)]; unfold u U transit;simp [n,map_sub,add_comm v _]
    rw [price,zpow_zero,zpow_zero,mul_one,mul_one,pin,run,sprite_val,inv_mul_eq_div, norm_div,norm_pow]; let m:=‖castG A n (U i) z‖; rw [← he]; change m / ‖t‖^d' ≤ _; rw [Real.norm_of_nonneg ht.le,le_div_iff₀ (pow_pos ha _)]
    calc _ ≤ m/t^d'*(t*r)^d':= by gcongr
         _ = m*r^d':= by rw [mul_pow]; field_simp
         _ ≤ _:= hj
end YM.PositionX.Chir.Dock
