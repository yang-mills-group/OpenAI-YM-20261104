import YM.LocalTaylorR2.Exponent.Dun

/-!
 # ReadyAll including WHOLE reserve at tilted Big plus all global push. Make actual arithmetic transfer & meter. Separation and ≤ enough supports.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open PhysicalNext.Repeat Reel Strand Candle Tender Mesh LocalTaylorR2.Price Charge RG01.Survive
variable (H:Cash W s μ L Q o C T R)(Ξ : Observatory G)
variable (U:H.ThinP){q:Orders k}
lemma liner {χ:Chi} (he:q≠Candle.perch k) (hv:live H U)(f:Bevy T):
    issue H f χ U q=∑ i ∈ univ.filter (fun i:Paint U.val k=>chooseSlot i=q), episode H χ U.val (rafters f i):=by
   ext V; rw [Mesh.issue,if_neg he,Mesh.ode,if_pos hv,Finset.sum_apply]; exact Finset.sum_congr rfl (fun i hi=>by dsimp only; rw [cups H f i (ne_of_eq_of_ne (mem_filter.mp hi).2 he)] ) -- direction?
lemma pristine (q:Orders k) : Mesh.issue H (weightLog H) χ U q=sprig H χ U q:= by
   have hp (q:Orders k) : Mesh.ode H (weightLog H) χ U q=Candle.script H χ U q:= by
     ext V; unfold ode Candle.script; split; swap; · rfl
     unfold convolve; apply Finset.sum_congr rfl; intro i _; dsimp only; rw [show Mesh.warm H (weightLog H) i=letters H i from ?_]; funext F X w; apply prod_congr rfl; intro j _; unfold absorb; split; next he=> simp
     next _=> rfl
   unfold Mesh.issue Candle.sprig; simp_rw [hp]
lemma noHope (h:¬ live H U)(f:Bevy T)(q:Orders k) : Mesh.issue H f χ U q=Candle.sprig H χ U q:= by ext V; simp only [Mesh.issue,Candle.sprig, Mesh.ode,Candle.script, if_neg h]
-- at rank zero no motion EXACT even when high partners might be frozen
lemma placid (t:Bevy T) (y:Bevy T): Mesh.issue H t χ U (0:Orders k)=Mesh.issue H y χ U (0:Orders k):= by
 by_cases hz:live H U; swap; · rw [noHope H U hz t,noHope H U hz y]
 have he:(0:Orders k)≠Candle.perch k:=fun h=> by have h : 0=k+1:=congr_arg Fin.val h; omega
 rw [liner H U he hz, liner H U he hz]; refine sum_congr rfl (fun i hi=>?_); rw [show rafters t i=rafters y i from ?_]; funext F X v; apply prod_congr rfl; intro j _; have hb : min (k+1) (inserts i)=0:=congr_arg Fin.val (mem_filter.mp hi).2; have hc : (i j).val+1 ≤ inserts i := single_le_sum (f:=fun s=>Series.rank (i s)) (fun _ _=>Nat.zero_le _) (mem_univ j); omega

variable {b t w A' r D' V' e ρ θ ζ c':ℝ} (N:Captain H j b t v w A A' r D' e (n+j) χ) (hB:LocalBookingsR2 ζ c' N.conduit)(M:StoresR2 H j v t A D l x n χ) (F': Wealth Ξ H V' n x l m N.conduit k ρ)
local notation "Θ" t=> replay (weightLog H) (Ξ.upgrade H k) (dial t*ρ^k)
local notation:max "Ig" i:max => Mesh.issue H i χ U (l:=k)
local notation "Z!"=> schemePrice (l:=k) N D x θ U
include M F' U
omit M in
lemma lineage (V:Config G c) (he: q ≠ Candle.perch k) (hV:Healthy (Pressure.temp s) (H.smallAt U) V): Filled ⊤ q.val dial (fun t=> memo V (Ig (Θ t) q)):=
   atRod H N _ (fun i=> population (Port.Burst.fat (logTest H i)) (F'.stuff _) dial (ρ^k)) U V hV he
lemma kiosq (t: Strand) (i: Orders k) (he:i≠ Candle.perch k) (hθ:1≤θ) :
   Items H U (Ig (Θ t) i) ∧ ∀ (V:Config G c), Healthy (Pressure.temp s) (H.smallAt U) V→ Ore V (Ig (Θ t) i) v (Z! i) j:=by
   let X:= Θ t; let V:= N.conduit; have hp: Lodestar H m V' V X:= F'.invests t
   by_cases h: live H U; swap
   · rw [Mesh.fallow H _ χ U h he]; refine ⟨⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩,fun V hV E _ _ _ Z x hv hx=> (Brush.certified zero_le_one (0:ℝ)).climb (norm_zero.le.trans (LocalTaylorR2.Price.positional N M hθ _ _)) le_rfl⟩
   rw [liner H U he h]; let Z:=univ.filter fun x:Paint U.val k=> chooseSlot x=i; let f (x:Paint U.val k):= episode H χ U.val (rafters X x)
   have heq (j:↥Z) := j.property
   let U' := H.smallAt U
   have ht (q:Paint U.val k): Port.Burst H U' (rafters X q):= glow (H:=H) _ q _ (Subset.refl (H.unionP U.val)) (fun i _=>hp.love _)
   have hx q:= episodeSitesBurst H (p:=U.val) (ht q) χ
   refine ⟨⟨?_,?_,?_⟩,fun V hv=>?_⟩
   · intro g T; rw [Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_congr rfl (fun i _=> (hx i).2.2 _ _)
   · show Measurable (∑ x∈Z,f x); simpa only [← Finset.sum_apply] using (Finset.measurable_fun_sum (f:=f) Z (fun i _=>(hx i).1))
   · intro V V' hV; rw [Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=> (hx i).2.1 V V' hV
   have hr:1≤r:= N.conduit.active; have hb:0≤2*r*(k+3:ℝ):=(by positivity); unfold schemePrice; rw [if_pos h]
   have he (q:Paint U.val k) (Hq:q∈Z):= episodeCostBurst H N.oboe U.2.2 (ht q) (Rates.elans H F'.bank M (tall (Ξ:=Θ t) (H:=H) hp F'.positively q U.val (Subset.refl U.val) h.1.2 (show inserts q ≤ k from ?_) hθ) F'.positively (forgeN _ hθ _) hb) V hv
   · intro E _ _ _ V x ht hV; simp only [Function.comp_def,Finset.sum_apply]; exact Brush.spree _ (fun q x=> f q (V x)) _ zero_le_one (fun i hi=> he i hi E V x ht hV)
   have hy : min (k+1) (inserts q)=i.val:=congr_arg Fin.val (mem_filter.mp Hq).2
   have hV:i.val≠ k+1:= fun heP=> he (Fin.ext heP); omega
end YM.LocalTaylorR2.Exponent
