import YM.SignedWilsonExpansion.F9.Costume
/-!
# Sonar grade & payer ready. Change.Layout only here, already bounded before real sympathy
No requirement of normed instances on future space/scheme. `poke`
 gives dual estimate; need algebra cone unipotency in Gram after earned rank signs. Cap projection.
-/
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
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MarqueQ
open SignedWilsonExpansion.Commission Method Method.Epic Asymptotics Stair MergeTrip Looms
open Normalize (Sec)
open XSpace.Cirrus
variable {W':Initialize G}{Q':∀ h,Rays G h W'.hol}{Ω:Council F}
variable {P':Hol G}{ι:Type}
abbrev sonar (F:Frame G h)(x:F.Index) := (F.basis.coord x) ∘ₗ ladderS h
lemma mote {t':ℕ}(β:(F.level h).Index)(X:Sec G h)(x:X∈ BideW Rι t') (v:t'≤ wr Rι β) : sonar Rι β X=0:= x β v -- t' nat insert
lemma breathe_up (X:Sec G d) (w:d≤h)(α:(F.level d).Index) : sonar Rι (upL F w α) (Normalize.up w X)=sonar (F.level d) α X:=by
    unfold sonar; rw [LinearMap.comp_apply,← On.raised w X]; apply fare_up F
lemma nearer (β:(F.level h).Index)(w:d≤h)(x:Sec G h)(l:d< wt Rι β)(t:x∈ Folia G d h): sonar Rι β x=0:=by
    let y:Sec G d:= ⟨x.val,t⟩; rw [show x=Normalize.up w y from rfl]; let u:= ladderS d y; have hf:ladderS h (Normalize.up w y)= raiseLabel G w u:= (On.raised w y).symm
    rw [sonar,LinearMap.comp_apply,hf,← (F.level d).basis.sum_repr u]; simp only [map_sum,map_smul]; apply Finset.sum_eq_zero; intro i _; rw [← climb F w i,show ((F.level h).basis.coord β) _=0 from (?_),smul_zero]
    rw [ show ((F.level h).basis.coord β) _ = _ from (show ((F.level h).basis.coord β) ((F.level h).basis (upL F w i))=(F.level h).coords ((F.level h).basis (upL F w i)) β from rfl),Frame.coords_basis]; rw [Pi.single_eq_of_ne]; intro t
    have hx: wt Rι (upL F w i) ≤d:= (congr_arg Prod.fst (up_grade F w i)).trans_le ((F.level d).bound i); rw [t] at l; omega
lemma criterionH {p:Sec G h}(x: ∀ j: (F.level h).Index, sonar Rι j p=0) : p=0:=by
    rw [← bulb_recovers G h p, show XSpace.On.sectionMap h p=0 from ((F.level h).coords).injective (by ext1 i; rw [map_zero]; exact x i),map_zero]
lemma pops (β α:(F.level h).Index)(i:ℕ)(g:wt Rι β=i)(v:wt Rι α≠ i) : sonar Rι β (vista F α)=0:=by
    rw [carried]; apply (F.level h).power_coefficient _ _ (projector_grade ((F.level h).pure α)); intro k; exact v ((congr_arg Prod.fst k).trans g)
lemma assembleParts (α:(F.level h).Index)(x:Sec G h)(w:wt Rι α=i) :
    sonar Rι α x= sonar Rι α (Normalize.en (show i≤h from w ▸ ((F.level h).bound α)) (Normalize.part h i x)):=by
    let V:= F.level h; let p(j:V.Index):= V.coords (ladderS h x) j; have ht:x=∑ j: V.Index,p j • vista F j:=by nth_rw 1 [←bulb_recovers G h x,← V.basis.sum_repr (On.sectionMap h x)]; rw [map_sum]; unfold vista p; simp only [map_smul]; refine Finset.sum_congr rfl fun i _=>congr_arg _ (carried ..).symm
    rw [ht]; simp_rw [map_sum,map_smul]; refine Finset.sum_congr rfl fun a _=> (?_); apply congr_arg (p a • ·); by_cases h: i=wt Rι a;
    · have hu (w:ℕ)(hw:w=wt Rι a)(ha:w≤ _): Normalize.en ha (Normalize.part _ w (vista F a))=vista F a:=by subst w; unfold vista; rw [Normalize.part_same]
      rw [hu i h]
    rw [pops α a _ w (Ne.symm h),vista, Normalize.part_other _ h _,map_zero,map_zero]
section layouts
namespace PorchK
variable (x:PorchK W' F Q' Ω R h k u)(q:ι→PorchK W' F Q' Ω R h k u)(Wn:Normalize.Store G)
variable {Y B:ι→ℝ}{L:Filter ι}(hQ:Annual q L Y)
-- `layout` gradient.M µ budgets power.V β scale tooth each booth leg.
lemma Salary_realComplex {M:Type}[AddCommGroup M][Module ℂ M][Module ℝ M][IsScalarTower ℝ ℂ M][FiniteDimensional ℝ M](p:ι→ M) (h:Maxer L Y)(t: Salary L Y B ℝ p): Salary L Y B ℂ p:=by
   let T:=Module.finBasis ℝ M; have hx(j:ι):p j= ∑ i, ((T.repr (p j) i:ℝ):ℂ) • T i:=by simp_rw [show ∀ (x:ℝ)(y:M),(x:ℂ) • y=x • y from (fun x y=> IsScalarTower.algebraMap_smul ℂ x y),T.sum_repr]
   show Salary L Y B ℂ p; refine Salary.via (Salary.many h _ Finset.univ (fun i _=> Salary.tilt (Wage.reals.mp (t (T.coord i))) (Salary.born (T i)))) (Eventually.of_forall fun i=> (hx i).symm) (by simp)
def slides : Module.End ℂ (Sec G h):=(Wn.layout W' x.mesh h 0).val
lemma deck1 : coeff 0 (Normalize.deck (Wn.layout W' x.mesh h))=1+ x.slides Wn:=by rw [coeff_zero_eq_constantCoeff_apply,Normalize.const_deck]; rfl
include hQ
lemma slide_rate (x:Expense.Stretched L (fun i=> (q i).mesh)) : Salary L Y (fun i=> (q i).mesh.spacing) ℂ (fun i=>(q i).slides Wn):=by
   let M:= Module.End ℂ (Sec G h); let p(i):= Wn.layout W' (q i).mesh h 0; let B':= Module.finBasis ℝ (Normalize.Change G h)
   have hz:= (Wn.nested_solution W' h x).1; unfold Expense.Rate at hz; simp only [sub_zero, Pi.zero_apply] at hz -- inspect
   letI:FiniteDimensional ℝ M:= Module.Finite.trans ℂ M
   apply Salary_realComplex _ hQ.1; refine Salary.pass (E:=Normalize.Change G h) (K:=ℝ) (F:=Module.End ℂ (Sec G h)) (P:=p) ?_ ((Normalize.Change G h).subtype); apply Salary.sufficient hQ.1 B'; intro i; exact Wage.enroll ((IsBigO.of_bound' (Eventually.of_forall fun j=>norm_le_pi_norm (Normalize.guide G h (p j)) i)).trans hz) -- craft
lemma slides_mark (x':Expense.Stretched L (fun i=> (q i).mesh))(Pp:∀ i≤e,Across L Y ℂ (fun j=>(q j).toEpic.tenor W' Wn i))(β:(F.level h).Index) :
    Salary L Y (fun i=> (q i).markW) ℂ (fun j=>(q j).canv.boots W' Wn (q j).mesh β (q j).l (q j).r (q j).ρ 0 - (q j).paid.originalT W' (q j).mesh (q j).ρ 0 ((F.level h).basis β)):=by
     let ε(i):=(q i).mesh.spacing; let Z(i):=(q i).paid.originalT W' (q i).mesh (q i).ρ 0 ((F.level h).basis β); let boot(i):= (q i).toEpic.tenor W' Wn 0 ((F.level h).basis β); let X(i):=(q i).slides Wn; simp_rw [boots_at]; have hB:Salary L Y 1 ℂ boot:= Across.salary ((Pp _ (Nat.zero_le e)).arrow (LinearMap.applyₗ _)); have ht: Salary L Y ε ℂ (fun i=> X i (boot i)):=by simpa only [one_mul] using Salary.matrix_full hQ.1 X hB (slide_rate q Wn hQ x')
     have he:= (Wn.nested_solution W' h x').2; change Salary L Y _ ℂ (fun i=> boot i-Z i); refine Salary.transfer (Y:= fun i=> (q i).markW) (B:=ε) (Salary.via (Salary.negative ht) (?_) (.refl ..)) (Wage.enroll (IsBigO.of_norm_le fun i=> ?_))
     · filter_upwards [he] with i hi; have hZ:=tenorEq W' (q i).toEpic hi.1; unfold Epic.tenor at hZ; rw [deck1 Wn (x:=q i)] at hZ; change -X i ( boot i )= boot i-Z i; rw [show Z i=boot i+ X i (boot i) from DFunLike.congr_fun hZ _]; abel
     change ‖(q i).mesh.spacing‖≤_; rw [Real.norm_of_nonneg (q i).mesh.positive.le,(q i).align]; exact anti_sizeT R.draws (q i).pos (q i).endo
end PorchK
end layouts
end MarqueQ
end YM.WilsonCoeffUV.Mer.Xa
