import YM.SignedWilsonExpansion.Grid.Masked
import YM.SignedWilsonExpansion.FourierGaussian
namespace YM.SignedWilsonExpansion.Overlap.Fair
/-! common axial angular mean for the two ports. Signed Klein flips
and the cycle C3. Handles plane `02` symmetrically with `12`. `mag` measures
total transverse momentum. Exact linear price constraints under *simultaneous*
π² across the panel. No claims of continuum group law or covariance UV outside
projected port. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView HighRank HighScale MarkRows MassShift MarkShift AxisChoice
open PhasePair Align Curtain
open scoped Classical Topology ContDiff BigOperators
local notation "P" => FourP
local notation "μ" => covMeasure Axis
local notation "Z" => Momentum.sq
local notation "A" => Axis
abbrev I := Fin 3 × Axis
abbrev spin : Equiv.Perm Axis:= ( Equiv.swap 0 1 ).trans (Equiv.swap 0 2)
abbrev spin3 : Fin 3→Equiv.Perm Axis:= ![Equiv.refl _,spin,spin.symm]
abbrev dip (t:Axis)(k:Axis): Prop:= t≠0∧k+1≠t∧k≠3
-- t=1..3 chooses all flips except (t−1 and time axis). handle Fin.succ cast
noncomputable instance (t k:A) : Decidable (dip t k):= by unfold dip; infer_instance
def flip (t:A)(p:P):P:= fun i=> if dip t i then -p i else p i
def mix (i:I)(p:P):P:= receive ( spin3 i.1 ) ( flip i.2 p )
variable (i:I) (k:A)(p q:P)
lemma turnNeg : flip k (-p)= -flip k p:= by funext i; simp only [flip,Pi.neg_apply]; split_ifs <;> simp only [neg_neg]
lemma negPor : mix i (-p)= -(mix i p):= by unfold mix; rw [turnNeg, Align.flipped]
lemma turnOwn : flip k (flip k p)=p:= by funext i; unfold flip; split_ifs <;> simp only [neg_neg]
lemma normW : Z ( flip k p )=Z p := by unfold Momentum.sq flip; exact Finset.sum_congr rfl fun i _=> (by split_ifs <;> ring )
private lemma fleet : MeasurePreserving (flip k) μ μ:= by
   have hr : MeasurePreserving (flip k) volume volume:= by
     apply volume_preserving_pi ( f:=fun  i (x:ℝ)=> if dip k i then -x else x ); intro i; by_cases he: dip k i; · simp_rw [if_pos he]; exact Measure.measurePreserving_neg volume
     simp_rw [if_neg he]; exact MeasurePreserving.id _
   refine ⟨hr.measurable,?_ ⟩; rw [ show μ=( ENNReal.ofReal Gaussian.capμ ) • volume from Gaussian.land, Measure.map_smul, hr.map_eq]
lemma awake : MeasurePreserving (mix i) μ μ:= ( sameM _ ).comp (fleet i.2)
lemma enclose : MeasurableEmbedding (mix i):= ( receiveE _ ).comp (( fleet i.2 ).measurable.measurableEmbedding ( Involutive.injective (turnOwn i.2) ) ) -- Lean dot
lemma timeπ : mix i p 3=p 3:= by rcases i with ⟨x,t⟩; fin_cases x <;> simp [mix,spin3,spin,receive,flip,dip,Equiv.swap_apply_def]
lemma magπ : Z (mix i p)= Z p:= Eq.trans (Align.same _ _) (normW _ _)
lemma billπ (d:ℝ): Tone.bill (FourierGaussian.axis d) (mix i p)=Tone.bill (FourierGaussian.axis d) p:= by rw [ FourierGaussian.bill_act, FourierGaussian.bill_act,timeπ]
def mag (p:P):ℝ:= p 0^2+p 1^2+p 2^2
def cost (p:P):ℝ:= 2*mag p/3
local notation "D" => Fair.cost
lemma costV : D (mix i p)= D p:= by unfold Fair.cost; have he:= magπ i p; unfold Momentum.sq at he; simp_rw [ qAxis,timeπ ] at he; unfold mag; congr 2; linarith
lemma costN : D (-p)=D p:= by simp [Fair.cost,mag]
-- quadrature takes real and complex (π means of κZ etc)
def price (p:P): (P→ℂ) →ₗ[ℂ] ℂ where
    toFun f:= (∑ i:I,f (mix i p))/12
    map_add' f g:=by simp only [Pi.add_apply, Finset.sum_add_distrib,add_div]
    map_smul' c f:=by simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul,← Finset.mul_sum,mul_div_assoc]
local notation "π" => Fair.price
def realP (p:P)(f:P→ℝ): ℝ:= (∑ i:I,f (mix i p))/12
lemma currency {p:P}{f:P→ℂ}{c:ℂ}(h:∀ i:I,f (mix i p)=c)(g:P→ℂ): π p (fun p=>f p*g p)=c*π p g:= by
    unfold Fair.price; simp only [LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [ h,← Finset.mul_sum, mul_div_assoc ]
lemma price_fix {p:P}{f:P→ℂ}{c:ℂ}(h:∀ i:I,f (mix i p)=c): π p f=c:= by unfold Fair.price; simp only [LinearMap.coe_mk,AddHom.coe_mk,h, Finset.sum_const, Finset.card_univ,Fair.I,Fintype.card_prod,Fintype.card_fin]; ring
lemma priced (f:P→ℝ): π p (fun k=>↑(f k))=( realP p f:ℂ ):= by unfold Fair.price realP; simp
-- sum exact 3 spatial axes moments. design bracket sum which simplifies.
def story (p:P)(f:P→ℝ):ℝ:= ∑ i:I,f (mix i p)
lemma sumS (J:A)(he:J≠3): story p (fun p=>p J^2)=12*(mag p/3):= by
   unfold story
   change (∑ i:Fin 3 × Axis,_)=_
   simp_rw [ Fintype.sum_prod_type, qAxis,Q3 ]
   rcases Radial.D4 J with rfl|rfl|rfl|rfl<;> first| contradiction| ( simp (disch:=decide) [ Fair.mix, flip,receive,spin3,Fair.spin, Equiv.swap_apply_def, dip, mag]; ring )
lemma sold (f g:P→ℝ) : story p (fun p=> f p+g p)=story p f+story p g:= by unfold story; rw [ Finset.sum_add_distrib ]
lemma saleV : π p (fun p=> ↑(AxisChoice.disk p))=( D p:ℂ ):= by -- AxisChoice.disk=disk
    rw [ priced ]; apply congr_arg; unfold realP; change (story p AxisChoice.disk)/12= _; unfold AxisChoice.disk; rw [ sold, sumS p 1 (by decide),sumS p 2 (by decide) ]; unfold Fair.cost; ring
local notation "Q" => fun (m:Bool) u p=> Energy.leg (degreeX m) 2 u p
local notation "e" => Align.vane
local notation "T" => Align.tune
variable (m j:Bool)
local notation "Qπ" => (fun m j=>Q m (e m j))
-- explicit raw cubature. To keep heartbeats down use intermediate general moments.
lemma settleX (J:A)(h:J≠3): story p (fun p=>p J)=0:= by
   unfold story
   change (∑ i:Fin 3 × Axis,_)=_
   simp_rw [ Fintype.sum_prod_type, qAxis,Q3 ]
   rcases Radial.D4 J with rfl|rfl|rfl|rfl<;> first| contradiction| ( simp (disch:=decide) [ Fair.mix, flip,receive,spin3,Fair.spin, Equiv.swap_apply_def, dip] )
-- relations product for distinct coordinate.
private lemma settleLT (J K:A)(h:J<K): story p (fun p=>p J*p K)=0:= by
   unfold story
   change (∑ i:Fin 3 × Axis,_)=_
   simp_rw [ Fintype.sum_prod_type,qAxis,Q3 ]
   have hh : ∀ J K:A,J<K →  ( J=0∧ K=1 ) ∨  ( J=0∧ K=2 ) ∨  ( J=0∧ K=3 ) ∨  ( J=1∧ K=2 ) ∨  ( J=1∧ K=3 ) ∨  ( J=2∧ K=3 ):= by decide
   rcases hh J K h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩; all_goals (simp (disch:=decide) [ Fair.mix, flip,receive,spin3,Fair.spin, Equiv.swap_apply_def, dip])
lemma settleY (J K:A)(h:J≠K): story p (fun p=>p J*p K)=0:= by
    rcases h.lt_or_gt with hv|hv; · exact settleLT p J K hv
    rw [ show (fun p:P=>p J*p K)=(fun p=>p K*p J) from funext (fun _=>mul_comm ..) ]; exact settleLT p K J hv
private lemma J0 (J:A)(h:J≠3): (∑ i:I,mix i p J)=0 := settleX p J h
private lemma J1 (J:A)(h:J≠3): (∑ i:I,mix i p J • mix i p) =(6*D p:ℝ) • unitV J:= by
   funext i; simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; change story p (fun p=> p J*p i)=6*D p*unitV J i
   by_cases he:i=J; · rw [he]; simp only [← pow_two,sumS p J h]; simp [unitV,spike,Fair.cost]; ring
   rw [ settleY p J i (Ne.symm he) ]; simp [unitV,spike,he]
lemma monA (k:P)(m:Bool): Qπ m false k = - k 2:= by cases m <;> simp [Energy.leg,Align.vane,degreeX]
lemma monB (k:P)(m:Bool): Qπ m true k=k (degreeX m):= by cases m <;> simp [Energy.leg,Align.vane,degreeX]
lemma less3 : degreeX m ≠3:= by cases m <;> decide
lemma monPay : (∑ i:I,Qπ m j (mix i p) • mix i p )=(6*D p:ℝ) • T m j:= by
   cases j; · simp_rw [monA,neg_smul,Finset.sum_neg_distrib,J1 p 2 (by decide) ]; simp [Align.tune]
   simp_rw [monB,J1 p (degreeX m) (less3 m) ]; rfl
lemma mon0 : (∑ i:I,Qπ m j (mix i p))=0:= by
    cases j; · simp_rw [ monA, Finset.sum_neg_distrib,J0 p 2 (by decide),neg_zero ]
    simp_rw [ monB,J0 p (degreeX m) (less3 m) ]
lemma monAd (f:P→ₗ[ℝ] ℂ): π p (fun p=> (Qπ m j p) • f p)= ( D p /2:ℝ ) • f (T m j):= by
   unfold Fair.price; simp only [LinearMap.coe_mk,AddHom.coe_mk]; simp_rw [ ← map_smul f,← map_sum, monPay ]; rw [ map_smul,map_smul ]; simp_rw [ Complex.real_smul ]; push_cast; ring
lemma story_zero : π p (fun p=> ↑( p 0*p 1 ))=0:= by rw [priced,realP]; change ((↑( story p (fun p=>p 0*p 1)/12 ):ℂ))=_; rw [ settleY p 0 1 (by decide) ]; norm_num
lemma antipode (f:P→ℂ): π p (fun p=> f (-p))= π (-p) f:= by simp [Fair.price, negPor]
-- continuum swaps with finite π.
variable {f:P→ℂ}
lemma price_int (h:Integrable f μ): Integrable (fun p=>π p f) μ:= by unfold Fair.price; simp only [LinearMap.coe_mk,AddHom.coe_mk]; exact (integrable_finsetSum _ fun i _=> (( awake i ).integrable_comp_emb (enclose i)).mpr h).div_const _
lemma pack_int (h:Integrable f μ): (∫ k,π k f∂μ)=(∫ k:P, f k∂μ):= by unfold Fair.price; simp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [integral_div,integral_finsetSum _ ( fun i _=> show Integrable (fun p=> f (mix i p)) μ from ((awake i).integrable_comp_emb (enclose i)).mpr h ) ]; simp_rw [ (awake _).integral_comp (enclose _) f, Finset.sum_const, Finset.card_univ ]; norm_num [Fair.I]
lemma price_rote (f:P→P→ℂ)(h:∀ x, Integrable (f x) μ): π p (fun p=>∫ k,f p k∂μ) = ∫ k, π p (fun p=> f p k)∂μ:= by unfold Fair.price; simp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [integral_div, integral_finsetSum _ (fun i _=> h _ )]
end
end YM.SignedWilsonExpansion.Overlap.Fair
