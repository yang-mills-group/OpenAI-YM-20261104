import YM.RGLocalTaylor.Retain.Assets
/-!
# CostE relative response - release at any authenticated Transfer-frame
Physical price; including all positive-order derivative costs in applicable setting.
Mark partners in Inputs remain *untouched*, separate contribution.Ineligibility loops unchanged.
Read at p=J or even at H=.actual.Do not assume Bose/Beam data along alignment
 equal WITHOUT `stamps` same Φ unit data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Trees
open PhysicalNext.Repeat.Daisy.Charity.RG12
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
namespace Retain
open Match RG01.Survive Post Read
open Mayer goodK Mill Fort
namespace Gala
variable {ε α θ K δ e d₁ g u w vJ uJ γ w' turn: ℝ} {M m:ℕ}  -- remove
set_option quotPrecheck false
local notation "p'" => Mayer.arcRadius G L s
local notation "δB" => (Fort.dust G L s)
local notation "ξM" => creditStencil M θ p'
local notation "fB" => Fort.vest G L s
local notation "O" => Chi.canonical
variable {f₁ f₂:glyph G f}
variable {N: Captain H j C' d v Y A b r B q n Chi.canonical}
    (hU : Upkeep P Q L s)
    (h : Threads H N uJ vJ e d₁ K θ δ g w turn k l M m)
    (hp: R.activities.E=f₁+f₂)
    (hv:0<a)(hm:a≤1)

structure NotesE (H :Cash W s μ L Q o C T R) (N:Captain H j C' d v Y A b r B q n O)(K :ℕ)
   (x:glyph G f) (f:Head S→ℝ) (b δ g θ α w:ℝ)(l:ℕ)(uJ e :ℝ): Prop where
   accepts : Quoted N.conduit K f θ (Mayer.arcRadius G L s) α A b (physical H K) (mantle H x K)
   grain : let v:= Mill.final_bill (H:=H) (fun p=> Mill.billBase H p f j l e uJ α (creditStencil K θ (arcRadius G L s))) K
           Ready H.smallAt (radiusB s) (fun i=>2^j*v i) (g+δ) w δ (1/2)
   sail : ∀ {ι:Type} [_f:Fintype ι](M':ι→Lotus.Leaf R)(rA:ι→ℝ), Merge.Palette.Plot M' H rA →
           let v:= Mill.final_bill (H:=H) (fun p=> Mill.promo M' rA p f e uJ α (creditStencil K θ (arcRadius G L s)) H j l) K
           Ready H.smallAt (radiusB s) (fun i=>2^j*v i) (g+δ) w δ (1/2)

-- hL extends tenure
lemma speed (hm:M≥1) (h:Awning H N.conduit A b d₁ e uJ vJ k l): vJ≤patchPrice r vJ M:= by
   apply le_trans (le_mul_of_one_le_right h.cSc (by exact_mod_cast hm : 1≤(M:ℝ))); apply le_add_of_nonneg_left; have ht:=N.conduit.active; positivity
include h hU hp hm hv
variable (X:Cash W s μ L Q o C T (impulse R f₂ a))
local notation "N'" => bead θ M
local notation "α'" => patchPrice r vJ M
local notation "v₀" => (collars G δ s j m*(w*(1-1/2)⁻¹))
local notation "Δ" => creditStencil M N' p'

lemma estimates (X:Cash W s μ L Q o C T (impulse R f₂ a)): ∃ E Z:ℕ→ℝ, dual H f₂ a E Z ∧ shelved X Z ∧ NotesE H N M f₁ (Fiber N.conduit (E+Z) (vest G L s)) (a / vest G L s) δ g (bead θ M) (patchPrice r vJ M) w l uJ e:= by
   obtain ⟨E,Z,hp',ht,hF,hX⟩:= skyline (H:=H) hU hm hv X
   let fP := Fiber N.conduit (E+Z) (vest G L s); let u:=a / fB
   have htU := worksStencil (Ξ:=N.conduit) hp' h.ht h.vote h.approved h.health h.effort hU.scale hX hp
   have hC' : Trees.degreePrice (radiusB s) (Mill.hill Q L μ s e uJ α' N' p' j l M) δ ≤ 1/2:= h.noteH ▸ h.checkE
   have hr:outlets H (E+Z) (δB+δB):= combination ht hF
   refine ⟨E,Z,hp',?_,⟨htU,?_,fun M' rA hh=>?_⟩⟩
   · obtain ⟨x,hx⟩:=hp'.bill; exact hx
   · intro v; rw [h.noteH]; apply Mill.axisOne h.ht htU.gradeF h.checkK hC' h.width h.pos; exact Fort.funding hU N.conduit hr h.check'
   intro v; rw [h.noteH]; apply axisTwo h.ht htU.gradeF M' rA hh.live h.checkK hC' h.width h.pos; exact Fort.payroll hU M' rA hh N.conduit hr h.check' h.fuzzy

omit hv hm hp
section layers
variable (p:BudgetPoint)(hy : preExponent p≤g) (hT:p.threshold=Pressure.temp s)(hj:p.order≤j)(hB:p.B=radiusB s)(hb:p.power≤ m)
variable {f':Head S→ℝ}
    {V:Rep G f} {J:Cash W s μ L Q o C T V}
    (A': Match.Alliance J H 1 0) (hA : A'.units=Equiv.refl _)
local notation "LP" => orient p (Beam.marquee J p).reg
open Gorge
local notation "St" => Gorge.stamp H A'
local notation "U₁" => Read.field (Gorge.nextG H M) (Gorge.cover H (physical H M) (χ:=O))
local notation "wE" => Read.field (Gorge.nextG H M) (Gorge.cover H (Fort.mantle H f₁ M) (χ:=O))
local notation "S!" => (p'^2)⁻¹ *γ
local notation "b₀" => (turnFee p)
include hb hj hT hy hB
omit hU
lemma funds' (hθ:NotesE H N M f₁ f' γ δ g N' α' w l uJ e)(hf:turnFee p=turn)(ht:1≤M): LP (St (U₁-wE)) S!:= by
   have hS:Sailor G p.threshold q j:=by rw [hT]; exact ⟨fun c x hh=> N.weigh.stroke c x (hh.trans N.talent)⟩
   have hg := Gorge.first_time (χ:=O) p hT hj hb hB N.income hS N.near N.position h.ht (speed ht h.ht) hθ.accepts (Gorge.nextG H M) (r₁:=2) (fun i g h=> h.1) hy h.pos (hB.symm ▸ hθ.grain)
   apply orient.widen (recording p A' hg); rw [mul_left_comm, hf]; exact mul_le_of_le_one_right (mul_nonneg (by have hx:= h.health; positivity) hθ.accepts.defect) h.price'
end layers
section trial
variable {V:Rep G f} {J:Cash W s μ L Q o C T V} (A':Match.Alliance J H 1 0)(Y':Match.Alliance J X 1 0)
   (hA:A'.units=Equiv.refl _)(hh:Y'.units=Equiv.refl _) (p:BudgetPoint)(hy:preExponent p ≤ g)(hT:p.threshold=Pressure.temp s)(hB:p.B=radiusB s)
   {D:Stage}(hT':Heavings D G L s)(hf:M≥2)(hM:Gates H δ g w (turnFee p) p.order M p.power)
   (hV:R.activities.E=f₁+f₂)

local notation "LP" => orient p (Beam.marquee J p).reg
local notation "St" => Gorge.stamp H A'
local notation "φM" => (Gorge.cover H (physical H M) (χ:=O))
local notation "V!" => (Gorge.cover H (Fort.mantle H f₁ M) (χ:=O))
local notation "ξM" => (Gorge.cover X (physical X M) (χ:=O))
local notation "t_" => dividend G D s
local notation "β'" => Time.credit G D*δE s
open Gorge
omit h hU
include hA hT' hf hM hy hT hB
-- isolated head from IMPULSE with Halt plusone prior.Just on resulting cost.
lemma shift (hP:Passport H g w' (turnFee p) δ p.order p.power M)(hr:Collection.Local (Beam.marquee J p) p (Height.serve J A' O (Beam.lit J)) u ε):
    LP (St (iconOnly H (Read.field (fun _ b=> b=1) φM))) (u+(t_+t_)):=by
   obtain ⟨hX,x,y,e,d₁,K,θ,A,b,C',d,v,Y,r,B,q,k,l,n,N,hL⟩:=hM
   have hh: ∃ X:Cash W s μ L Q o C T (impulse R R.activities.E 1), True:= by
      rw [show impulse R R.activities.E 1=R from (by unfold impulse Post.imprint; simp)]; exact ⟨H,trivial⟩
   let S:= Classical.choose hh; have hV': R.activities.E=0+R.activities.E:= (zero_add _).symm
   obtain ⟨x,y,h,hS,hθ⟩:= estimates hX hL hV' zero_lt_one le_rfl S -- arguments order hv hm?
   have hg:=funds' hL p hy hT le_rfl hB le_rfl A' hθ rfl (by omega : 1≤M)
   apply iconicPrice (H:=H) p A' hA (by omega) hr (orient.widen hg hT'.unmark) (orient.widen (Gorge.costEra H p A' hy hL.pos hT hB hP) ?_)
   exact le_trans (inv_anti₀ (pow_pos (zero_lt_one.trans_le hT'.live) _) (pow_le_pow_right₀ hT'.live (by omega))) hT'.margin

include hV hv hm hh
lemma temperatures (hq:Gates X δ g w (turnFee p) p.order M p.power)(he: Passport X g w' (turnFee p) δ p.order p.power M)(hu:Collection.Local (Beam.marquee J p) p (Height.serve J Y' O (Beam.lit J)) ((3/16:ℝ)*(Time.credit G D*δE s)) ε):
   LP (St (Read.field (floors H M) φM - Read.field (floors H M) V!)) ((a/4)*(Time.credit G D *δE s)):= by
   have ht:= shift (H:=X) Y' hh p hy hT hB hT' hf hq he hu
   obtain ⟨hX,uJ,vJ,e,d₁,K,θ,A,b,C',d,v,Y,r,B,q,k,l,n,N,hL⟩:= hM
   obtain ⟨E,Z,h,hS,hθ⟩:= estimates hX hL hV hv hm X
   have hE:= value_L H X (N:=N) p A' Y' (by omega) hA hh hV h hT le_rfl hB ht hS (funds' hL p hy hT le_rfl hB le_rfl A' hθ rfl (by omega)) -- order
   let f:= β'; have hx : 0< f/64:= hT'.benefit; have hF: 0≤f:=by linarith
   apply orient.widen hE; let t:= (p'^2)⁻¹; change a*((3/16:ℝ)*f+(f/64+f/64))+t*(a/fB) ≤ a/4*f
   have hy:t*(a/fB) = a * (t*(1/fB)):= by ring
   have hθ:= mul_le_mul_of_nonneg_left hT'.unmark hv.le
   rw [hy]; nlinarith only [show a*(t*(1/fB))≤ a*(f/64) from hθ, mul_nonneg hv.le hF]
end trial
end Gala
end Retain
end YM.RGLocalTaylor
