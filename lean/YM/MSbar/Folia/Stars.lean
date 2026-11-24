import YM.MSbar.DeltaM.Town
import YM.MSbar.Pulse.Spot
import YM.MSbar.Lease.Bench
import YM.MSbar.Folia.Life
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Film
open Function Filter MeasureTheory Cacao Whisk Kelvin RG Lattice Wilson Tree
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar Analysis Bakery Lattice Precision Push.Uniform
open Next.SectorChange Heath Bulk Heath.Stock Heath.Cottage
variable {G : Gauge} {c f:Side}{S:StepData c f}{p a :ℕ}
    {T W A B t s u α β Z:ℝ}
set_option quotPrecheck false
variable (J:Voice G) (F : Forest S.ratio)
variable (X Y: Support f) (V: Config G c) (U : Config G f)
local notation "I"=> board F X
local notation "A!"=>↥(board F X)
local notation "ρ!"=> fence F (board F X) G -- ambiguous
local notation "Z!"=> Config G f
local notation "W!"=>IV F (board F X) G
local notation "X!"=> SpaceP F X G
variable (m: SpaceP F X G)
local notation "K!"=>draw F X U m t
variable (ν : Positions (Key F G))(γ:ChartRatio G)
local notation "Y!"=> hotel F X Y J V ν A B
variable (R:Rep G f)(i:S.Choices)
local notation "L"=> rental F J R Y i V ν
local notation "z!"=> clipM F X Y Y! γ t m U
variable (g:LocalRatio γ) (C:Matrix (↥(board F X)× G.ColorIndex) (↥(board F X)× G.ColorIndex) ℝ) 
local notation "φ!"=> fLog F X γ t
local notation "Γ"=> Portal.purse z! (fun w:X!=> fLog F X γ t w m U (rental F J R Y i V ν) C)
local notation "ρ"=>fieldLaw C
local notation "q!"=> twirl F (board F X)
-- absolute slice axes

def imageNear (W:Config G f) : Positions (Key F G):= (tint G _).symm (fun i:F.Free=> J.decode (W i.val))
def stretch (W:Positions (Key F G)): Config G f:= F.drape (fun u:F.Free=> G.lieExp (tint G _ W u))
-- inputs K bound center.J radii reserve.Outreach.
variable {K H δ w ω' j B' κ ι ψ : ℝ}
structure Couch (J:Voice G)(F:Forest S.ratio)(ν: Positions (Key F G))(Y :Support f)(g:ChartRatio G)(v:F.Free→G.Color) (V:Config G c) (A B K H W :ℝ) : Prop where
    ht : ‖ν‖+B ≤ K
    glued : 0 < A
    lifts : A ≤ B
    sums (i:F.Free) :‖v i‖ ≤ shade G*K
    emits (i:F.Free) : G.lieExp (v i)= Precision.replica S.ratio V i.val
    enroll1 : 4* (shade G*K) ≤ H
    enroll2 : H ≤ J.r
    enroll3 : H < g.radius
    enroll4 : 2*J.C*H≤ J.δ
    round : J.C*H^2 ≤ W
    final : W ≤ shade G*K
variable (hV:Clear G J)(v:F.Free→G.Color) (hS :Couch J F ν Y γ v V A B K H W) (hP:X ⊆Y)
local notation "Yθ"=> Y!
local notation "Z0"=> chambers F Y J V ν
local notation "Q"=> imageNear J F
include hV hS hP
lemma anchors (Z:Config G f) (hU: Z∈ Y!) : let z:=Z0 Z; let s':= imageNear J F z
    z=stretch F s' ∧ ∀ i, tint G _ s' i∈ Metric.ball 0 γ.radius ∧ ‖tint G _ s' i-tint G _ (rented F Y J V ν Z) i-v i‖≤W :=by
   intro z s'; have hB:=leanOn F X Y J _ _ hV hP hU hS.lifts (hS.glued.le.trans hS.lifts)
   let u:= rented F Y J V ν Z
   let b:=tint G _ u; let a:=shade G*K; have he:‖u‖≤K:=by rw [show u=u-ν+ν from (sub_add_cancel u ν).symm]; exact ((norm_add_le ..).trans (add_le_add hB le_rfl)).trans ((add_comm ..).trans_le hS.ht)
   have hh (i:F.Free): ‖b i‖≤ a:= (norm_le_pi_norm (tint G _ u) i).trans ((tint_le u).trans (mul_le_mul_of_nonneg_left he (shade_pos G).le))
   let w:=tint G _ s'; have hA:0≤a:=mul_nonneg (shade_pos _).le ((norm_nonneg _).trans he); have hl:= hS.enroll1; have hΩ:a ≤ H:= by linarith only [hl,hA]
   have hc(i:F.Free): z i.val=G.lieExp (b i)*G.lieExp (v i):=by rw [hS.emits]; exact F.off_tree _ i
   have he (i:F.Free): G.chord (z i.val)≤ J.δ:=by
       have he(x:G.Color)(hi:‖x‖ ≤a) : G.chord (G.lieExp x)≤ J.C*H:= ((hV.small x (hi.trans (hΩ.trans hS.enroll2))).2).trans (mul_le_mul_of_nonneg_left (hi.trans hΩ) (zero_le_one.trans hV.cost)); rw [hc]; exact (G.chord_triangle ..).trans ((add_le_add (he _ (hh i)) (he _ (hS.sums i))).trans (by linarith only [hS.enroll4]))
   have hp(i:F.Free): w i= J.decode (z i.val):=by unfold w s' imageNear; rw [ContinuousLinearEquiv.apply_symm_apply]
   refine ⟨?_,fun i=>?_⟩
   · funext i; unfold stretch; by_cases hi:i∈F.trunks; unfold z chambers lifting; exact (F.on_tree _ ⟨i,hi⟩).trans (F.on_tree _ ⟨i,hi⟩).symm
     let k:F.Free:=⟨i,hi⟩; change z k.val= F.drape _ k.val
     rw [F.off_tree]; change _=G.lieExp (w k); rw [hp,(hV.near (z k.val) (he k)).2.1]
   have ht: ‖w i-b i-v i‖ ≤ W:=by
       rw [hp,hc]; apply (hV.turns _ _ H hS.enroll2 ((hh i).trans hΩ) ((hS.sums i).trans hΩ)).trans; apply (mul_le_mul_of_nonneg_left ((hh i).trans hΩ) (mul_nonneg (zero_le_one.trans hV.cost) (hA.trans hΩ))).trans; exact (le_of_eq (by ring : J.C*H*H=J.C*H^2)).trans hS.round
   refine ⟨?_,ht⟩
   apply Metric.mem_ball.mpr; rw [dist_zero_right]; apply lt_of_le_of_lt (b:=H) _ hS.enroll3; change ‖w i‖ ≤ H
   have hm: w i=w i-b i-v i+b i+v i:=by abel
   nth_rw 1 [hm]; apply (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add ht (hh i))) (hS.sums i)).trans ?_); linarith only [hS.final,hA,hl]
lemma coverage : Set.MapsTo (fun t:IV F (board F X) G => t) {z| q! z U∈hotel F X Y J V ν A B} (covered γ (orbitJ F X U)):=by
   intro t he i hi; let x:= q! t U; obtain ⟨hU,hz⟩:=anchors J F X Y V ν γ hV v hS hP (q! t U) he
   have hy:x∈ Y!:=he; let D:=rented F Y J V ν x
   let b:= fareX F J V x i.val; have hk:i.val∈board F Y:= Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP ((Finset.mem_filter.mp i.prop).2)⟩; have ht:tint G _ D i.val=b:=by unfold D rented; rw [ContinuousLinearEquiv.apply_symm_apply]; rw [if_pos hk]; -- equality
   have h₁:=boarding F X Y J V ν hV hP hy hS.lifts _ hk
   have h₂:G.lieExp b=flume F V x i.val:=h₁.1
   let W₀:= Z0 x; let d:= tint G _ (imageNear J F W₀) i.val; have hp:W₀ i.val.val=G.lieExp d :=by nth_rw 1 [show W₀=_ from hU]; exact F.off_tree _ _ -- cast?
   have hv : W₀ i.val.val= canoe (S:=S) F x i.val.val:=by
       unfold W₀ chambers lifting; rw [F.off_tree]; change G.lieExp (tint G _ D i.val)*_= _; rw [ht,h₂]; unfold flume; simp
   have hl:t i *canoe (S:=S) F U i.val.val= canoe (S:=S) F x i.val.val:=by unfold x twirl;rw [stationary, pegged]; rw [dif_pos i.prop]
   change t i∈(fun x=> x * orbitJ F X U i) '' _; refine ⟨_,⟨d,(hz i.val).1,rfl⟩,?_⟩; unfold orbitJ; rw [←hp,hv,←hl]; group
end YM.MSbar.Bakery.Film
