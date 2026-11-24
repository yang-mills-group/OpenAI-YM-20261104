import YM.SignedWilsonExpansion.F9.Vicar
/-! # Per order & rank lead estimator cost. Subpower of μ-height wages sufficient. -/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MarqueQ
namespace PorchK
open SignedWilsonExpansion.Commission Method Method.Epic Asymptotics Stair MergeTrip Looms
open Normalize (Sec)
open XSpace.Cirrus
variable {W':Initialize G}{Q':∀ h,Rays G h W'.hol}{Ω:Council F}
variable {P':Hol G}{ι:Type}
variable (x:PorchK W' F Q' Ω R h k u)(q:ι→ PorchK W' F Q' Ω R h k u)(Wn:Normalize.Store G) {S:SectionData (F.level d)} (hS:S.Sound P')(p0: Bid.pop S)(v₀:d≤h)
variable {Y τ g μ ν:ι→ℝ}{L:Filter ι}
-- ν for rank price from Voters. ≺ Z=poly Y. Keep hyp uniform on meshes Ω through epoch.Vol.O.Pilot. absorb all η slack later.
structure FrontQ (q:ι→ PorchK W' F Q' Ω R h k u)(L:Filter ι)(Y g μ ν:ι→ℝ): Prop where
    pol : Annual q L Y
    stretch : Expense.Stretched L (fun i=>(q i).mesh)
    ahead : Y=O[L] μ
    inside_ : Maxer L μ
    mass (n:ℕ) : Tendsto (fun i=> μ i^n * (q i).markW) L (𝓝 0)
    decays (n:ℕ) : Tendsto (fun i=> μ i^n*g i) L (𝓝 0)
    slope (n:ℕ) : Tendsto (fun i=> Y i^n*ν i) L (𝓝 0)
variable (Bf:FrontQ q L Y g μ ν)
variable (Pp:∀ i≤e, Across L Y ℂ (fun j=>(q j).toEpic.tenor W' Wn i))
variable (α:(F.level d).Index)(i:(F.level h).Index)
lemma mark_pos : 0<x.markW:= sizeT_pos _ x.pos _
abbrev billSize (x:PorchK W' F Q' Ω R h k u)(d:ℕ):= (x.markW^d)⁻¹
abbrev duty (x:PorchK W' F Q' Ω R h k u)(d:ℕ): ℂ:= (x.billSize d:ℂ)
lemma owed (q:ι→ PorchK W' F Q' Ω R h k u)(d:ℕ): Wage L Y (fun i=> (remitW q d i)⁻¹) (fun i=>(q i).duty d):= Wage.reals.mp ( Wage.enroll ( isBigO_refl _ L ) )
lemma restore_one (x:PorchK W' F Q' Ω R h k u)(d:ℕ): x.duty d*(x.markW:ℂ)^d=1:=by unfold duty billSize; push_cast; rw [inv_mul_cancel₀]; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr x.mark_pos.ne')
-- scope actual Deal.P inserted ater.
include Pp Bf hS p0 v₀
lemma earSolo (j o:ℕ)(hj:j≤e)(g:wt Rι i=o): Wage L Y (remitW q o) (fun a=> sonar Rι i ((q a).sober Wn S α j)):=by
    simp_rw [show ∀ a,sonar Rι i ((q a).sober Wn S α j)=_ from (fun a=>assembleParts i _ g)] -- loops? x matches sub expression? RHS has no direct sonar arg  
    exact ((upper_bills q Wn Bf.pol _ hS p0 v₀ α Pp j o (g ▸ ((F.level h).bound i)) hj).pass (Normalize.en (show o≤h from g ▸ ((F.level h).bound i)) )) (sonar Rι i)
lemma solo_equal (g:wt Rι i=d)(a0:wt (F.level d) α=d)(u':wr (F.level d) α≤ wr Rι i): Tendsto (fun a=> (q a).duty d * sonar Rι i ((q a).sober Wn S α 0)) L (𝓝 (sonar Rι i (vista F (upL F v₀ α)))):=by
    have hv:= owed (L:=L) (Y:=μ) q d; let t:= fun a=> (q a).duty d * sonar Rι i ((q a).sober Wn S α 0); let k':= sonar Rι i (vista F (upL F v₀ α)); have pay (n:ℕ) : Tendsto (fun a=> μ a ^ n * ((remitW q d a)⁻¹ * remitW q (d+1) a)) L (𝓝 0):=by
        refine (Bf.mass n).congr (fun a=>?_) -- theorem statement? usually Tendsto.congr' eventualEq
        unfold remitW; rw [pow_succ,←mul_assoc ((_)⁻¹),inv_mul_cancel₀ (pow_ne_zero _ (q a).mark_pos.ne'),one_mul]
    rcases lt_or_eq_of_le u' with t₀|u
    · have he:wr Rι (upL F v₀ α)<wr Rι i:= (congr_arg Prod.snd (up_grade F v₀ _)).trans_lt t₀; rw [mote i _ (vista_rank (F:=F) (upL F v₀ α) he) le_rfl]; exact Wage.next_zero (Wage.mul hv (Wage.transfer (lamp_small q Wn Bf.pol Bf.stretch Pp S hS p0 v₀ α i g t₀) Bf.ahead)) pay
    have hx:= Wage.transfer (lamp_equal q Wn Bf.pol Bf.stretch Pp S hS p0 v₀ α i a0 g u) Bf.ahead; let X':= fun a=> sonar Rι i ((q a).sober Wn S α 0) - ((q a).markW :ℂ)^d * k'
    have he(a): (q a).duty d*X' a+k'= t a:=by unfold X'; rw [ mul_sub, ←mul_assoc,restore_one,one_mul,sub_add_cancel]
    simpa only [zero_add] using (((Wage.next_zero (Wage.mul hv hx) pay).add_const k').congr he) -- `+const` unknown
-- assemble assigned color coefficients. `y_th` and `ξ`, input basis.V` b.Property. t vs ht.Crop. Rank exact sign cost and precision. Assembly.
structure SizeW (L:Filter ι)(μ:ι→ℝ)(F:Frame G d)(x:ι→ F.Coeff): Prop where
     paid (i:F.Index) : Wage L μ 1 (fun j=> x j i)
structure Crest (L: Filter ι)(Y ν θ:ι→ ℝ)(F:Frame G d)(x:ι→ F.Coeff)(r:ℕ)(u:F.Coeff): Prop where
     pure (i:F.Index) : u i≠0 → F.grades i=(d,r)
     campus (i:F.Index) (hp:r ≤ wr F i): Wage L Y ν (fun j=> x j i - (θ j:ℂ)*u i)
     head : Tendsto θ L (𝓝 1)
-- stamp uses y_th == h_*^(cap) placed th. Fully includes cap unit.
abbrev resource (x:PorchK W' F Q' Ω R h k u)(S:SectionData (F.level d))(y:(F.level d).Coeff): (F.level d).Coeff:= x.duty d • y
abbrev account (x:PorchK W' F Q' Ω R h k u)(S:SectionData (F.level d))(y:(F.level d).Coeff): Tape (Sec G h):= x.canv.snapD W' S Wn x.mesh x.l x.r x.ρ (x.resource S y)
variable {x':ι→(F.level d).Coeff} (t_: SizeW L μ (F.level d) x')
omit hS p0 v₀ Bf Pp in
lemma accounting (i':ℕ)(y:(F.level d).Coeff): account Wn x S y i'=∑ j:(F.level d).Index,(x.duty d*y j) • x.sober Wn S j i':=by unfold account snapD; simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]; rfl
include t_
lemma account_bill (j n:ℕ)(v:n ≤ h)(w:j≤e): Salary L μ (fun a=> ((remitW q d a)⁻¹ * remitW q n a)) ℂ (fun i=> Normalize.part h n (account Wn (q i) S (x' i) j)):=by
    simp_rw [accounting,map_sum,map_smul]; apply Salary.many Bf.inside_; intro i _; have hh:= Salary.shift (upper_bills q Wn Bf.pol _ hS p0 v₀ i Pp j n v w) Bf.ahead; apply Salary.via (Salary.tilt (Wage.mul (owed (Y:=μ) (L:=L) q d) (t_.paid i)) hh) (.refl ..); refine Eventually.of_forall fun a=>?_ ; change (remitW q d a)⁻¹ * 1 * _= _; rw [mul_one]
end PorchK
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa
