import YM.FVA2.Arrival.Schedule
/-!
# Assemble the actual `Uses` setup on `XSpace` geometries

E.g. `marches`: take the filter of `Sample`s (varying mesh, layout and
center; using a gate condition, see `YM/XSpace`). Use those **same** placements
in the Trial. To work with their geometry hypotheses, change the Trial on the
initial portion of the filter not meeting the hypotheses (see `lease`).

`entries`: bare regulator **including mark fees**, before *position* normalization. `rate`
already compares to MS in these geometries (see `testP` and `Dposition`: the continuum
positions see the **same** offsets on the test profile). The mass parameter `μ`
in `Arrival.Schedule` uses the logarithmic convention of `Teller/Mass.lean`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Arrival.Schedule
open Function Filter Set Finset Metric MeasureTheory Real Lattice
open MS MS.Local.Physical MS.Tide MS.Tide.PeakT MS.Fleet MS.Orbit MS.Vista MS.Vane MS.Tone MS.Rake MS.Land MS.Dial
open XSpace.Cirrus Press Change
open scoped Topology ContDiff Classical
variable {n:ℕ} {G:Gauge}
local notation "U"=> Fin n
local notation "Z"=> XSpace.Cirrus.Sample n
variable (μ:ℝ)(z:Points n)(h:z∈conf n)
local notation "T"=> showR (n:=n) μ
private def Protect (p: Z): Prop:= Sized p ∧ Clamp (plot z) (testP ( showR μ ) p) ∧ ∀ w:U, ‖testP ( showR μ ) p w‖ ≤ 1+‖plot z w‖
include h
private lemma invested : ∀ᶠ p in Gate z, Protect μ z p := by
 let p:= plot z; obtain h':=track h; obtain he:= lookG μ z; apply (weather z).and ((he.eventually (earlyW (p:=p) h')).and (eventually_all.mpr fun w=> ?_)); refine ((((tendsto_pi_nhds.mp he w).norm).eventually ( gt_mem_nhds ?_ ))).mono fun i hi=> le_of_lt hi; change ‖plot z w‖ < 1+_; linarith
private def lease (p: Z) := if Protect μ z p then p else (invested μ z h).exists.choose
lemma lease_eq : lease μ z h=ᶠ[Gate z] id:= (invested μ z h).mono fun _ hi=> if_pos hi
private lemma lease_own (p:Z) : Protect μ z (lease μ z h p):= by unfold lease; split; assumption; exact (invested μ z h).exists.choose_spec
/-- The MS `Trial`, same actual regulator choices from the outset except for early indices
that don't meet spacing/momentum hypotheses. -/
def performance : MS.Dial.Trial (XSpace.Cirrus.Sample n) (Fin n) where
 profile:=⟨ (T).profile.θ ∘ lease μ z h,(T).profile.η ∘ lease μ z h, fun _=>(T).profile.room _ ⟩
 head := (T).head ∘ lease μ z h
 side := (T).side ∘ lease μ z h
 off i := (T).off i ∘ lease μ z h
local notation "P"=> performance μ z h
lemma marches : Uses (performance μ z h) (Gate z) μ:= by
 let f:=lease μ z h; let p:=P; have hx:Tendsto f (Gate z) (Gate z):= tendsto_id.congr' (lease_eq μ z h).symm
 let i := track h; refine ⟨ fun j=>?_ , unpose ( v:=μ ) p.off ?_,fun _=>rfl,(speed z).comp hx,fun i=>hx.eventually (boom μ z i),fun i=> cleared (f i) ((lease_own μ z h i).1), Vista.centered_size _ _ fun i=> (bar_lift (f i) (lease_own μ z h i|>.1)).symm⟩
 · refine ⟨ 1+ ‖plot z j‖, by positivity,fun i=>?_⟩; let a := exp ( p.profile.θ i ); have hi:= ( lease_own μ z h i ).2.2 j; change ‖exp ( -p.profile.θ i ) • Tone.embed (p.off j i)‖ ≤ _ at hi; rw [Real.exp_neg,norm_smul_of_nonneg (by positivity)] at hi; change _ ≤ _*a; rw [mul_comm]; exact (inv_mul_le_iff₀ (by unfold a; positivity)).1 hi
 intro u v hu; let A:=plot z; let d:= ‖A u-A v‖; have hd:0<d:= norm_pos_iff.mpr ( sub_ne_zero.mpr ( i.ne hu ) ); refine ⟨ ⟨2*d,by positivity, fun k=> ?_⟩,⟨d/2,by positivity,fun k=> ?_⟩ ⟩ <;> rw [show MS.Rake.Geo.roots ( frameF _ μ ) _=1 from exp_zero,mul_one]; · exact ((lease_own μ z h k).2.1 u v hu).2.le
 exact ((lease_own μ z h k).2.1 u v hu).1.le
omit h

section Dreg
-- Compare exactly with values at familiar (common arbitrary real center shift).
-- No rounding error here, by translation symmetry already in the `book` reading.
variable {B: Local.Physical.Deck G} (u:Fin n→Label B){K:Booked B}(S:MS_Data G K)
lemma same_multi {I W:Type} [LinearOrder W] (p q: Rake.Position W I) (H:∀ i j,p i - p j=q i - q j)(μ:I→Measure QP) (K L:Planet G I) (f g:Rake.Site G I)(A:Rake.Dance G I W)(k:ℕ)(s:Finset W): multi μ p K L f g A k s=multi μ q K L f g A k s:= by
 unfold multi; refine congr_arg (Rake.lonely K f g k + ·) ?_; apply sum_congr rfl; intro j hj; let h:= n_small hj; have hp:rootX p j-rootX p s=rootX q j-rootX q s:= by unfold rootX; rw [ dif_pos h.2.1,dif_pos (h.2.1.mono h.1.le),dif_pos h.2.1, dif_pos (h.2.1.mono h.1.le) ]; exact H _ _
 rw [hp]
lemma transfers {x y:U→QP}(hp:Injective x)(he:∀ i j,x i-x j=y i-y j): spine S u μ x=spine S u μ y:= by
 have hy:Injective y:= fun i j h=> hp ( sub_eq_zero.mp ( ( he i j ).trans (by rw [h, sub_self])) ); let U':= spine S u μ x; obtain hx:= pin S u μ hp; refine perfect (G':=rowM (frameF Unit μ) S ∘ u) ?_ ( pin S u μ hy ); refine ⟨ hx.1,hx.2.1,fun t h n=> ?_⟩; let p:=fun i (_:Unit)=>x i; let q:=fun i (_:Unit)=>y i; rw [ same_multi q p (fun i j=>funext fun k=>(he i j).symm) ]; exact hx.2.2 t h n

lemma Dposition (i:Z)(hz:Sized i)(hs:Injective (testP ( showR μ ) i)) : book S u μ (testP ( showR μ ) i)= book S u μ (plot ( familiar i )):= by
    unfold book; rw [transfers μ u S (y:=plot ( familiar i )) hs (fun j k=> by simp [planes _ μ _ hz.unit])]
end Dreg
local notation "B"=> Press.portDeck G
variable (Y:XSpace.Initialize G)(u:Fin n→Label (Press.portDeck G)){K:Booked (Press.portDeck G)} (S:MS_Data G K)(M: Land.Prescription (Press.portDeck G))
local notation "Ξ"=> MS.Tide.ApplyMF (wickInput Y) ( MS.Swirl.Near.Stripped M.team ) M u
variable (t:Finset (Fin n))(k:ℕ)
-- Physical report before applying the position normalization. Scale θ.
-- Input separately weighted by spacing, not the clipped exponential formula.
local notation "ι"=> (Label.h ∘ u)
local notation "m"=> charge (Label.h ∘ u) t
def entries (i: Z): ℂ:= ((i.F.spacing:ℂ)^(Vane.charge (Label.h ∘ u) t))⁻¹ * Top.value Y u M 0 i.layout i.F.p.side ( μ-theta i.F ) t k
local notation "E"=> entries μ Y u M t k
lemma wholeAt (x:ℝ)(s:Side)(L:Cover)(v:U→Cover) (i:Z)(h:∀ j,L+v j=i.layout j): Top.value Y u M L v s x t= Top.value Y u M 0 i.layout s x t:= by
 unfold Top.value; rw [show Top.declares u L v=Top.declares u 0 i.layout from ?_]; funext j; unfold Top.declares; rw [zero_add,h]
lemma meter {i:Z}(hz:Sized i) : MS.Tide.higher (T).profile (Vane.charge ( Label.h ∘ u ) t) i=((i.F.spacing:ℂ)^( Vane.charge (Label.h ∘ u) t ))⁻¹:= by
 let a:= theta i.F; let x:=i.F.spacing; let h : exp (-a)=x:= bornS hz.unit; rw [Real.exp_neg] at h; change _=( ( (x:ℝ):ℂ )^_ )⁻¹; rw [←h]; unfold higher Port.τ; simp only [ inv_pow,inv_inv,zpow_natCast,Complex.ofReal_inv ]; exact Complex.ofReal_pow ..
variable (g:G.Simple)(ps: TaylorOKF S (Press.wickInput Y) M)
include h g ps
lemma rate : PeakT ( Gate z ) (T).profile Tide.mildG ( E - fun i=> tour S u μ (plot ( familiar i )) t k):= by
 obtain hP:= marches μ z h; obtain ⟨V,hV⟩:= check_tF S ( wickInput Y ) u P ps hP g true; obtain ⟨b,hb,hQ⟩:= ( hV.bouquet t k ).2; let p:=P; let f:= lease μ z h
 have hv (i:Z): fare ( Label.h ∘ u ) p.profile ( ordZ V ) t k i=entries μ Y u M t k ( f i ) := by
    let a:= f i; let H:= (lease_own μ z h i).1; let aH :=μ-theta a.F; let N:=psi a.F; let d:=Vane.charge (Label.h∘u) t; let x:= bar a
    have hL:= (Top.identifies Y u M x (σ a) (periodN N) aH t (⟨N.val,two_mul (α:=ℕ) N.val⟩)).1 (hV.cost i t);
    change higher (T).profile d a * _= ((a.F.spacing:ℂ)^_)⁻¹*_;
    rw [show ordZ V t k i = _ from congr_fun hL k, wholeAt Y u M t aH (periodN N) _ _ a (offset a), psi_back a.F, meter μ u t H];
 refine ⟨ b,hb,?_⟩; filter_upwards [hQ,lease_eq μ z h] with i hi he; have hu:= hv i; let q:=lease_own μ z h i; change f i=i at he
 have hG : testP p i=testP T i:= by change testP T ( f i )= _; rw [he]
 have hp: Sized i:= he ▸ (show Sized (f i) from (lease_own μ z h i).1); rw [he] at hu; have H:tour S u μ ( testP p i ) = tour S u μ (plot (familiar i)):= by rw [hG]; unfold tour; rw [Dposition μ u S i hp (hG ▸ micro p hP.knit i)]
 rw [ Pi.sub_apply, show fare ( Label.h ∘ u ) (P).profile _ _ _ _= _ from hu, H ] at hi; -- lake replace
 have hY : p.profile.θ i=(T).profile.θ i:= congr_arg ( T ).profile.θ he; unfold Tide.lake at hi ⊢; rw [show (P).profile.θ i= _ from hY] at hi; exact hi
end YM.FVA2.Arrival.Schedule
