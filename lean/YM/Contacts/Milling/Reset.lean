import YM.Contacts.Milling.Kindle
import YM.Contacts.Milling.BeamPrice
/-! Couplings compared as literal formal series. The relative charge inverse is not
 an infinitely many steps assumption. -/
namespace YM.Contacts.Milling.Resetter
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open Convoy Kale Ion Steam FreeResolvent Lumen
open PowerSeries
open scoped Topology BigOperators Classical Matrix NNReal ContDiff
noncomputable section
variable {α β Υ :Type}{s:ℝ≥0}{n k r j e:ℕ}{m:Side}{G:Gauge}
abbrev Pow := PowerSeries ℝ
def Uniform (U:Pow): Prop:= coeff 0 U=1
def QuietPower (U:Pow):Prop:=∀ i,i%2=1→coeff i U=0
def pin (U: Pow)(j:ℕ) : ℝ := coeff j U
def gap (A B:Pow)(j:ℕ) := ∑ i∈(antidiagonal j|>.filter (fun i :ℕ×ℕ=>0 < i.1 ∧ 0 < i.2)), pin A i.1 * pin B i.2
lemma gap_agrees (A B P Q:Pow)(n:ℕ)(h:∀ i<n,pin A i=pin P i)(hk:∀ i<n,pin B i=pin Q i): gap A B n=gap P Q n:= by
   apply sum_congr rfl; intro i he; obtain ⟨hl,ha,hv⟩:= mem_filter.mp he; have hh:=mem_antidiagonal.mp hl; rw [h i.1 (by omega), hk i.2 (by omega)]
lemma bolt_mul (A B:Pow) (n:ℕ)(h:0<n) : pin (A*B) n = pin A n*pin B 0+pin A 0*pin B n+gap A B n:= by
   unfold pin; rw [coeff_mul]; let F (i:ℕ×ℕ):= pin A i.1*pin B i.2; let S:= antidiagonal n; have he:(0,n)∈ S:= mem_antidiagonal.mpr (zero_add _); let Z:=(S.erase (0,n)).erase (n,0); have hp:(n,0)∈ S.erase (0,n):= mem_erase.mpr ⟨fun e=> (h.ne' (congr_arg Prod.fst e)), mem_antidiagonal.mpr rfl⟩; change (∑ i∈S,F i)=_; rw [← add_sum_erase S F he, ← add_sum_erase _ F hp]; have hb : Z= S.filter (fun i:ℕ×ℕ=>0 < i.1∧0 < i.2):= by ext ⟨i,j⟩; simp [Z,S,mem_antidiagonal]; omega
   change F _ + (F _ + ∑ i∈Z,F i)= F (n,0)+F (0,n)+ (∑ i∈ S.filter _, F i); rw [hb]; abel
lemma pin0_mul (U V:Pow):pin (U*V) 0=pin U 0*pin V 0:= by simp only [pin,coeff_zero_eq_constantCoeff, map_mul]
lemma Uniform.mul {U V:Pow} (h:Uniform U)(hv:Uniform V):Uniform (U*V):= by change pin _ _=_; rw [pin0_mul,(show pin U 0=1 from h),(show pin V 0=1 from hv), one_mul]
lemma uniform_one : Uniform 1:= by unfold Uniform; simp
lemma QuietPower.mul {U V:Pow}(h:QuietPower U)(hv:QuietPower V): QuietPower (U*V):= by
   intro i hi; rw [coeff_mul]; refine sum_eq_zero fun p hp=>?_ ; have he:=mem_antidiagonal.mp hp; by_cases h':p.1%2=1; · rw [h _ h',zero_mul]
   rw [hv _ (by omega),mul_zero]
lemma quiet_one : QuietPower 1:= fun i hi=> by rw [coeff_one,if_neg (by omega)]
def relative (V:Pow)(i:ℕ)(t:ℕ→ℝ):ℝ:= -- residual pin ℓ, energy U*R² uses power itself V
    let X:= PowerSeries.mk t; gap X X i + gap V (X*X) i
lemma bolt_square (U V:Pow)(h:Uniform U)(hv:Uniform V)(i:ℕ)(hi:0 < i): pin (U*V^2) i= pin U i+2*pin V i+ relative U i (pin V):= by
   rw [pow_two,bolt_mul U (V*V) i hi,bolt_mul V V i hi,(show pin U 0=1 from h), (show pin V 0=1 from hv),(show pin (V*V) 0=1 from hv.mul hv)]; unfold relative; rw [show PowerSeries.mk (pin V)=V from PowerSeries.ext fun j=> by rw [PowerSeries.coeff_mk]; rfl]; ring
lemma cost_rel (U:Pow) (V W: ℕ→ℝ)(n:ℕ)(h:∀ i < n,V i=W i) : relative U n V= relative U n W:= by
  let P (t:ℕ→ℝ):Pow:=PowerSeries.mk t; have he (u:ℕ→ℝ) j: pin (P u) j=u j:= coeff_mk _ _
  have hp (j:ℕ)(hj:j<n): pin (P V) j=pin (P W) j:= by rw [he,h j hj,he];
  change gap (P V) (P V) n + gap U (P V * P V) n=gap (P W) (P W) n+gap U (P W*P W) n; rw [gap_agrees (P V) (P V) (P W) (P W) n hp hp,gap_agrees U (P V*P V) U (P W*P W) n (fun _ _=>rfl) ?_]; intro i hi; unfold pin; rw [coeff_mul,coeff_mul]; apply sum_congr rfl; intro j hj; have hy:=mem_antidiagonal.mp hj; exact congr_arg₂ (·*·) (hp j.1 (by omega)) (hp j.2 (by omega))
def tempest (U:Pow)(n:ℕ) : ℝ:= if n=0 then 1 else -(pin U n+ relative U n (fun i=>if _h:i<n then tempest U i else 0))/2
termination_by n
def rotate (U:Pow): Pow:= PowerSeries.mk (tempest U)
lemma rotate_zero (U:Pow): Uniform (rotate U):= by rw [Uniform,rotate,coeff_mk,tempest,if_pos rfl]
lemma rotate_pin (U:Pow)(n:ℕ)(hn:0<n): pin (rotate U) n= -(pin U n + relative U n (pin (rotate U)))/2:= by
   rw [pin,rotate,coeff_mk,tempest,if_neg hn.ne']; rw [cost_rel U _ (pin (PowerSeries.mk (tempest U))) n ?_]; intro i hi; rw [dif_pos hi, pin, coeff_mk]
theorem rotate_share {U:Pow}(h:Uniform U): U*(rotate U)^2=1:= by
   apply PowerSeries.ext; intro i; cases i with
   | zero=> rw [sq,show coeff 0 (U*(rotate U * rotate U))=1 from (h.mul ((rotate_zero U).mul (rotate_zero U)))]; simp -- overloaded
   | succ i=> have hv:= i.succ_pos; change pin _ _=_; rw [bolt_square U (rotate U) h (rotate_zero U) _ hv,rotate_pin U _ hv,coeff_one,if_neg hv.ne']; ring
lemma rotated (A:Pow)(R:Pow)(ht:Uniform A)(hu:Uniform R)(H:A*R^2=1): R=rotate A:= by
   apply PowerSeries.ext; intro i; induction i using Nat.strong_induction_on with|h i ih=>
   by_cases h:i=0; · subst i; rw [(show coeff 0 R=_ from hu), (show coeff 0 (rotate A)=1 from rotate_zero A)]
   let x:=rotate A; change pin R i=pin x i; have hp:= congr_arg (fun p:Pow=>pin p i) (H.trans (rotate_share ht).symm); erw [bolt_square A R ht hu i (Nat.pos_of_ne_zero h), bolt_square A (rotate A) ht (rotate_zero A) i (Nat.pos_of_ne_zero h), cost_rel A (pin R) (pin (rotate A)) i ih] at hp; unfold x; linarith only [hp]
-- use reflection for parity
lemma quiet_rotate {A:Pow}(h:Uniform A)(hp:QuietPower A): QuietPower (rotate A) := by
 let R (A:Pow):=PowerSeries.rescale (-1) A; have ht i A: coeff i (R A)= (-1:ℝ)^i*coeff i A:= by simp [R]
 have he:R A=A:= PowerSeries.ext fun i=> by
    rw [ht]; by_cases hi:Even i
    · rw [hi.neg_one_pow,one_mul]
    rw [hp i (Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hi)),mul_zero]
 let v:=rotate A; have hy: R v=v:= rotated A (R v) h (show pin (R v) 0=1 from (ht 0 v|>.trans (by rw [(show coeff 0 v=1 from rotate_zero A)]; ring))) (by calc
   _ = R (A*v^2):= by unfold R; rw [map_mul,map_pow, (show PowerSeries.rescale (-1) A=A from he)]
   _ = _:= by rw [show A*v^2=1 from rotate_share h]; simp [R])
 intro i hi; have hh:= ht i v; rw [hy, (Nat.odd_iff.mpr hi).neg_one_pow] at hh; change coeff i v=_; linarith
-- charge κ: g_old^{-2} P_ℓr(log U) g_old^ℓ, ℓ = e+2-r
section reassemble
variable (w:Pow) {U:House α} (F:House α)
def charge (l:ℕ) (n:ℕ):= pin (w * (rotate w)^l) n
def ticker (i j:ℕ) := charge w i (j-i)
def dazzle (F:House α) : House α := fun j r=> if 2 ≤ j+r then F (j+r-2) r else 0 -- shift by (r-2)
def flipBack (F:House α) : House α := fun i r=> if r ≤ i+2 then F (i+2-r) r else 0
lemma flashing (h:Shaped F): flipBack (dazzle F)= F := by
   funext i r; unfold flipBack; split
   next he=> rw [dazzle,if_pos (by omega),show i+2-r+r-2=i by omega]
   next he=> exact (h.thin i r (.inr (by omega))).symm
-- rank unorder count; φ=ξ*rotate so charges with extra w
-- cost need subtraction even when invalid region automatically vanish.
def presage (F:House α)(j:ℕ): Rack α := fun r=> F j r-∑ i∈Finset.range j,ticker w i j • (if _h:i<j then presage F i r else 0) -- include w syntax?
termination_by j
def lowerHouse (F:House α): House α:= flipBack (presage w (dazzle F))
lemma presage_eq (j r:ℕ) : presage w F j r= F j r - ∑ i∈Finset.range j,ticker w i j • presage w F i r := by
  rw [presage]; congr! 1; exact sum_congr rfl fun i hi=> by rw [dif_pos (Finset.mem_range.mp hi)]
lemma presage_bot (r:ℕ): presage w F 0 r= F 0 r:= by rw [presage_eq]; simp
lemma presage_out {r j:ℕ}(h:j+r < 2) : presage w (dazzle F) j r=0:= by
   induction j using Nat.strongRecOn with| _ n ih=>
   rw [presage_eq, dazzle, if_neg (by omega),sum_eq_zero,sub_zero]; intro i hi; have he:= Finset.mem_range.mp hi; rw [ih i he (by omega),smul_zero]
lemma near_house {r j:ℕ} (hp:Uniform w) : dazzle (lowerHouse w F) j r=presage w (dazzle F) j r:= by
   unfold dazzle lowerHouse; split
   next h=> rw [flipBack,if_pos (by omega),show j+r-2+2-r=j from by omega]; rfl
   next hz=> exact (presage_out w F (by omega)).symm
lemma Uniform.power (h:Uniform w)(l:ℕ): Uniform (w^l):= by induction l with|zero=>rw [pow_zero];exact uniform_one|succ l ih=>rw [pow_succ]; apply ih.mul h
lemma port (h:Uniform w)(n): ticker w n n=1:= by rw [ticker,Nat.sub_self]; exact h.mul ((rotate_zero w).power (rotate w) n)
lemma charter (h:Uniform w)(i j:ℕ): pin (w*(PowerSeries.X*(rotate w))^j) i=if j ≤ i then ticker w j i else 0:= by
   rw [show w*((PowerSeries.X*(rotate w))^j)= w*(rotate w)^j * PowerSeries.X^j from (by ring)]; unfold pin; rw [coeff_mul_X_pow']; split <;> rfl
lemma rehouse (h:Uniform w)(i r:ℕ): dazzle F i r= ∑ j∈Finset.range (i+1), pin (w*(PowerSeries.X*(rotate w))^j) i • dazzle (lowerHouse w F) j r:= by
   simp_rw [charter w h i,near_house w F h]; rw [sum_range_succ,if_pos (by omega),port w h,one_smul,presage_eq w (dazzle F) i]
   rw [show (∑ x∈Finset.range i,(if x ≤ i then ticker w x i else 0) • presage w (dazzle F) x r) = _ from sum_congr rfl (show ∀ j∈Finset.range i,(if j ≤ i then _ else 0) • _ = ticker w j i • presage w (dazzle F) j r from fun x hx=>by rw [if_pos (Finset.mem_range.mp hx).le])]; abel
-- e-form explicitly resets only earlier powers
lemma translated {e r:ℕ}(hr:r≤e+2)(h:Uniform w): lowerHouse w F e r=F e r-∑ i∈Finset.range (e+2-r), ticker w i (e+2-r) • dazzle (lowerHouse w F) i r:= by
    rw [lowerHouse, flipBack, if_pos hr,presage_eq,dazzle, show e+2-r+r=e+2 from by omega, if_pos (by omega), Nat.add_sub_cancel] -- unfolds wrong
    apply congr_arg; exact sum_congr rfl fun i hi=> congr_arg (ticker w i _ • ·) (near_house w F h).symm
lemma presage_form (h:Shaped F)(u:Uniform w) : Shaped (lowerHouse w F):= by
    have hx j r : Poem (dazzle (lowerHouse w F) j r):= by
       induction j using Nat.strongRecOn with| _ j ih=>
         rw [near_house w F u,presage_eq]; rw [sub_eq_add_neg (dazzle F j r)]; apply Poem.add; · unfold dazzle; split; exact h.poem _ _; apply Poem.empty
         apply Poem.minus; exact Poem.sum _ fun k hk=>(Poem.scale (by rw [← near_house w F u]; apply ih k (Finset.mem_range.mp hk)) _)
    constructor
    · intro i j; unfold lowerHouse flipBack; split; rw [←near_house w F u]; apply hx; apply Poem.empty
    intro i r hi; unfold lowerHouse flipBack; split; swap; rfl
    next he=> rcases hi with ⟨hh,hp⟩|hh; swap; omega; subst i; rw [presage_eq, dazzle, show 0+2-r+r=2 from by omega,if_pos le_rfl,h.thin _ _ (Or.inl ⟨rfl,hp⟩),sum_eq_zero]; exact sub_zero _; intro j hj; rw [presage_out w F (by simp only [Finset.mem_range] at hj; omega), smul_zero]
variable {V:House (Node α)}{P Q:House α}
lemma presage_dorm {V :Equiv.Perm α}(h:Dorm V F): Dorm V (lowerHouse w F):= by
    have ht j (r:ℕ) x : presage w (dazzle F) j r (V∘ x)= presage w (dazzle F) j r x:= by
       induction j using Nat.strongRecOn with| _ j ih=>
         rw [presage_eq]; simp only [Pi.sub_apply,Finset.sum_apply, Pi.smul_apply]; apply congr_arg₂ (·-·); · unfold dazzle; split; exact h ..; rfl
         exact sum_congr rfl fun k hk=> congr_arg (fun x:ℝ=> ticker w k j • x) (ih _ (Finset.mem_range.mp hk))
    intro i j x; unfold lowerHouse flipBack; split; apply ht; rfl
lemma presage_frame (h:Cradle α V)(ht:Uniform w) : Cradle α (lowerHouse w V):= by
    refine ⟨presage_form w _ h.toShaped ht, fun i=> presage_dorm w _ (h.here _), fun i=>?_⟩; suffices hh:∀ i,presage w (dazzle V) i 0=0 by rw [lowerHouse,flipBack,if_pos (by omega),hh]
    intro i; induction i using Nat.strongRecOn with| _ i ih=> rw [presage_eq,sum_eq_zero,sub_zero,dazzle]; split; apply h.scalar;rfl; intro j hj; rw [ih j (Finset.mem_range.mp hj),smul_zero]
def led (w:Pow)(Q:TableFee)(r i:ℕ):ℝ:= Q i r+∑ j∈Finset.range i, ‖ticker w j i‖ * (if _h:j < i then led w Q r j else 0)
termination_by i
def ledBase (P:TableFee): TableFee:= fun i r=> if 2 ≤ i+r then P (i+r-2) r else 0
def ledCap (w:Pow)(P:TableFee): TableFee:= fun i r=> if r ≤ i+2 then led w (ledBase P) r (i+2-r) else 0
lemma ledFee (w:Pow)(Q:TableFee)(r i:ℕ): led w Q r i= Q i r+∑ j∈Finset.range i, ‖ticker w j i‖*led w Q r j:= by rw [led]; apply congr_arg; exact sum_congr rfl fun i hi=> by rw [dif_pos (Finset.mem_range.mp hi)]
variable {T:TableFee}
lemma precached (h:Roof s V T)(i r:ℕ): Pulse.Rooted (terrain s _) (dazzle V i r) (ledBase T i r):= by unfold dazzle ledBase; split; apply h.shelter; exact Pulse.Rooted.tranquility _
lemma hike (h:Roof s V T)(i r:ℕ): Pulse.Rooted (terrain s _) (presage w (dazzle V) i r) (led w (ledBase T) r i):= by
   induction i using Nat.strongRecOn with| _ i ih=> rw [presage_eq,ledFee]; exact Pulse.Rooted.sub (precached h _ _) (Pulse.Rooted.aggregate _ fun j hj=> (ih j (Finset.mem_range.mp hj)).smul _)
lemma budget_presage (h:Roof s V T): Roof s (lowerHouse w V) (ledCap w T):= by
   refine ⟨fun i r=>?_⟩; unfold lowerHouse flipBack ledCap; split; exact hike w h _ _; exact Pulse.Rooted.tranquility _
lemma data_presage (P:House (Co m α))(h:Roof s V T) (ht:∀ i r, Shadow (lower m) (V i r) (P i r)) (i r:ℕ): Shadow (lower m) (lowerHouse w V i r) (lowerHouse w P i r):= by
   have he i : Shadow (lower m) (presage w (dazzle V) i r) (presage w (dazzle P) i r) := by
      induction i using Nat.strongRecOn with| _ i ih=>
      rw [presage_eq,presage_eq w (dazzle P)];
      have hl: Shadow (lower m) (dazzle V i r) (dazzle P i r):= by unfold dazzle; split; exact ht _ _; exact Shadow.empty _
      have hw j (hj:j∈Finset.range i):= Pulse.Rooted.smul (hike w h j r) (ticker w j i); have hy:= Shadow.aggregate _ (Finset.range i) hw fun j hj=> (ih j (Finset.mem_range.mp hj)).scale (ticker w j i)
      rw [sub_eq_add_neg (dazzle V i r),sub_eq_add_neg (dazzle P i r)]; exact hl.add (by simpa only [neg_one_smul] using hy.scale (-1)) (precached h _ _) ( (Pulse.Rooted.aggregate _ hw).neg)
   unfold lowerHouse flipBack; split; apply he; exact Shadow.empty _
lemma precadence {m:Side}(h:Roof s V T)(ht: Cradle α V)(hg:Uniform w): hair (lowerHouse w V) m=lowerHouse w (hair V m):= by
   funext i r; by_cases h0:r=0; · subst r; rw [hair, (presage_frame w ht hg).scalar,printLull]; suffices hh:∀ i,presage w (dazzle (hair V m)) i 0=0 by rw [lowerHouse,flipBack,if_pos (by omega),hh]
                                  intro i; induction i using Nat.strongRecOn with| _ i ih=> rw [presage_eq,sum_eq_zero,sub_zero,dazzle]; split; rw [hair,ht.scalar,printLull]; rfl; intro j hj; rw [ih j (Finset.mem_range.mp hj),smul_zero]
   letI:NeZero r:= ⟨h0⟩; exact focused (printFeeds (heritage (fun p=> (presage_frame w ht hg).here p i r) _)) (lower_onto m) (data_presage w _ h (fun i r=> printFeeds (heritage (fun p=> ht.here p i r) _)) i r)
lemma glitter [Fintype α](F:House α)(x:House.Dir α)(i r) : design (dazzle F i r) x=grate F i r x:= by unfold dazzle grate; split; rfl; exact parcel_nil _
lemma recaptured [Fintype α](u:Uniform w)(i r:ℕ)(x:House.Dir α): grate (lowerHouse w F) i r x= grate F i r x -∑ j∈Finset.range i,ticker w j i * grate (lowerHouse w F) j r x:= by
   simp_rw [← glitter,near_house w F u]; rw [presage_eq w (dazzle F) i,parcel_sub]; apply congr_arg; simp only [design,verse_sum, map_sum]; exact sum_congr rfl fun _ _=> Convoy.design_scale ..
end reassemble
section guards
local notation "Ζ" => Swatch G m
local notation "R" => Link G m
variable {V P:Link G m→ℝ}
lemma truncated (h:Guards V k) (j:ℕ) (hj:j≤k): Guards (prepare j V) j:= by
   let W:=prepare j V; have he:Rays j (W-V):= dream j h.analytic; have ha: AnalyticAt ℝ W 0:=prepared ..; have hl (L : R →L[ℝ] R) (hl:∀ x,V (L x)=V x)(x:R): W (L x)=W x:= by unfold W prepare; exact sum_congr rfl fun i _=> (woven h.analytic L x i).symm.trans (congr_arg (fun f:R→ℝ=> jet f i x) (funext hl))
   refine ⟨continuous_iff_continuousAt.mpr (fun x=> (prepared ..).continuousAt),ha,fun u=> hl _ (h.color u),fun s=> hl _ (h.spins s),?_⟩
   let L : Ζ→R:=moveField; let P: Ζ→L[ℝ] R:= ContinuousLinearMap.snd ℝ _ _
   have hh: Rays j ((W-V)∘moveField-(W-V)∘ P):= (merkin (ha.sub h.analytic) he _ moveField_analytic moveField_zero).sub (merkin (ha.sub h.analytic) he _ (P.analyticAt _) (map_zero _))
   convert (hh.add (h.grade.weaker hj)) using 1; ext x; change W (moveField x)-W x.2 = W (moveField x)-V (moveField x) - (W x.2-V x.2) + (V (moveField x)-V x.2); abel
lemma preservesMinus (h:Guards V k)(hp:Guards P k) : Guards (V-P) k := ⟨h.cont.sub hp.cont,h.analytic.sub hp.analytic,fun u x=> congr_arg₂ (·-·) (h.color u x) (hp.color u x),fun u x=> congr_arg₂ (·-·) (h.spins u x) (hp.spins u x),by convert h.grade.sub hp.grade using 1; ext z; simp only [Pi.sub_apply]; abel⟩
lemma preservesTotal {P:Υ→ Link G m→ℝ} (s:Finset Υ)(h:∀ i∈s,Guards (P i) k): Guards (∑ i∈s,P i) k:= by
   let Y:= fun x=>∑ i∈s,P i x; change Guards _ _; rw [show (∑ i∈s,P i)=Y from funext fun i=> Finset.sum_apply ..]; refine ⟨continuous_finsetSum _ fun i hi=> (h i hi).cont, ContDiffAt.analyticAt (ContDiffAt.sum fun i hi=>(h i hi).analytic.contDiffAt),fun u x=> sum_congr rfl fun i hi=>(h i hi).color ..,fun u x=> sum_congr rfl fun i hi=>(h i hi).spins .., fun v=>?_⟩; unfold Y; simp_rw [← Finset.sum_sub_distrib]; exact Asymptotics.IsBigO.sum fun i hi=> (h i hi).grade v
lemma shining (h:Guards V k)(b:ℝ): Guards (b • V) k:= by
   have he : (b • V)=(fun x=> b* V x):= rfl; rw [he]; refine ⟨continuous_const.mul h.cont,analyticAt_const.mul h.analytic,fun u x=> congr_arg (b*·) (h.color u x), fun u x=> congr_arg (b*·) (h.spins u x),?_⟩; intro v; simp_rw [← mul_sub]; exact (h.grade v).const_mul_left _
variable {F: House (Lines G m 1)}
lemma seals (w: Pow)(ht:Uniform w)(h:sealed F k) : sealed (lowerHouse w F) k:= by
   let V:= lowerHouse w F; intro i hi; change Guards (wind V k i) (k-i); induction i using Nat.strongRecOn with| _ i ih=>
   let U (j:ℕ):= prepare (k-i) (wind V k j); let T:= Finset.range (k-i); let W j : Link G m→ℝ:= ticker w j i • U j; let M:=∑ j∈Finset.range i,W j; suffices he:wind V k i=wind F k i-M by
      rw [he]; refine preservesMinus (h i hi) (preservesTotal (P:=W) _ ?_); intro j hj; have hj:=Finset.mem_range.mp hj; exact shining (truncated (ih j hj (by omega)) _ (by omega)) _
   funext x; change (∑ r∈T,grate _ i r x)= _; unfold V M; simp_rw [recaptured w F ht i,Finset.sum_sub_distrib]; rw [sum_comm (s:=T), Pi.sub_apply, Finset.sum_apply]; apply congr_arg; refine sum_congr rfl fun j hj=>?_ ; have hj:= Finset.mem_range.mp hj; change (∑ r∈T, _)= _ * ∑ r∈T,jet _ _ _ ; rw [← mul_sum]; congr 1; refine sum_congr rfl fun r hr=> ?_; rw [wind_jet]; rw [if_pos (by unfold T at hr; simp only [Finset.mem_range] at hr; omega)]
end guards
section budget
variable (x:G.ColorIndex){F: bore G}{v: Bed}{T: TableFee}
def sink (F:bore G): Pow:= PowerSeries.mk fun i=>if i=0 then 1 else salvia G x (F i 2)
lemma sink_mast : Uniform (sink x F):= by rw [Uniform,sink,coeff_mk,if_pos rfl]
lemma central_preserves (hs:0<s) (ht:Blazing F v)(hw:Whole v.metric)(hv:v.metric.read 0=1) (hp:∀ m,(v.metric.acts m)ᵀ=v.metric.acts m)(h:Roof s F T):
   Blazing (lowerHouse (sink x F) F) v ∧ senior G x (lowerHouse (sink x F) F) := by
 let w:=sink x F; have hb: Light (lowerHouse w F):= ⟨presage_frame _ ht.frame (sink_mast _), by intro i j; rw [precadence w h ht.frame (sink_mast _)]; exact seals w (sink_mast _) (ht.beams j i)⟩; rotate_left
 let V:=lowerHouse w F; have he: V 0 2=F 0 2:= by unfold V; rw [translated w F (by omega) (sink_mast _)]; simp
 have hc : Blazing V v := ⟨hb.my,fun m=> ⟨cradle_shape hb.my,fun p=>by unfold hair; rw [he]; apply (ht.pri m).glow⟩,fun n i=> hb.protects i n⟩; refine ⟨hc,fun i hi=>?_⟩; change salvia G x (V i 2)=0; have hl: Roof s V _:= budget_presage w h;
 suffices hY: ∀ i, salvia G x (V i 2)= if i=0 then 1 else 0 by rw [hY,if_neg hi.ne']
 intro i; induction i using Nat.strongRecOn with| _ i ih=>
 by_cases h0:i=0; · subst i; rw [he,stark_cash hs hv ht h hw hp,if_pos rfl] -- wrong args
 have ht0 i : dazzle V i 2=V i 2 := by simp [dazzle];
 let A i := V i 2; let Z j:= ticker w j i • A j; let Ω:=∑ j∈Finset.range i,Z j; have hh: A i=F i 2-Ω:= by simpa only [A,Z, Ω, V, Nat.add_sub_cancel, dazzle, Nat.le_add_left 2, ↓reduceIte] using (translated w F (e:=i) (r:=2) (by omega) (sink_mast _));
 have fg j:=Pulse.Rooted.smul (hl.shelter j 2) (ticker w j i); have fj:=Pulse.Rooted.aggregate (Finset.range i) fun j _=> fg j; have hn:= salvia_finite x (u:=Z) (Finset.range i) (fun i _=>fg i) hs; change salvia G x (A i)=_; rw [hh,if_neg h0]; rw [sub_eq_add_neg,salvia_sum x (h.shelter ..) fj.neg hs,← neg_one_smul ℝ Ω, salvia_scale x fj hs]; rw [show salvia G x Ω= _ from hn]; simp_rw [show ∀ j, salvia G x (Z j)=_ from fun j=> salvia_scale x (hl.shelter j 2) hs (ticker w j i)]; rw [Finset.sum_eq_single 0]; swap; · intro j hj he; rw [ih j (Finset.mem_range.mp hj),if_neg he,mul_zero]
 swap; · intro he; simp at he; contradiction
 rw [(show ticker w 0 i=salvia G x (F i 2) from by unfold ticker charge pin w sink; simp [h0]), (ih 0 (by omega)), if_pos rfl]; ring
end budget
-- parity of through-ticket rule (track shifts of rank under loop contractions)
def Platinum (X:House α):Prop:=∀ i j,i%2≠j%2→ X i j=0
lemma sunk (x:G.ColorIndex)(F: bore G)(h: Platinum F): QuietPower (sink x F):= fun i hi=>by rw [sink,coeff_mk,if_neg (by omega),h i 2 (by omega),salvia_zero]
lemma charged (w:Pow)(h:Uniform w)(hg:QuietPower w)(j:ℕ): QuietPower (w* rotate w^j):= by
    refine hg.mul ?_; induction j with|zero=>rw [pow_zero]; apply quiet_one|succ i ih=> rw [pow_succ]; exact ih.mul (quiet_rotate h hg)
lemma lower_even (F:House α)(w:Pow)(h:Uniform w)(he: Platinum F) (hu:QuietPower w): Platinum (lowerHouse w F):= by
    have hh i (r:ℕ) (hp:i%2=1) : presage w (dazzle F) i r=0:= by
       induction i using Nat.strongRecOn with| _ i ih=> rw [presage_eq,Finset.sum_eq_zero,sub_zero, dazzle]; split; apply he; omega; rfl; intro j hj; by_cases he:j%2=1; rw [ih j (Finset.mem_range.mp hj) he,smul_zero]; rw [show ticker w j i=0 from charged w h hu j _ (by have hh:= Finset.mem_range.mp hj; omega),zero_smul]
    intro i j hj; unfold lowerHouse flipBack; split; apply hh; omega; rfl
lemma gathering_even {F:House α} {G:α→α→ℝ}(h:Platinum F) (p:ℕ) : Platinum (gathering G F p) := by
    induction p using Nat.strongRecOn with| _ i ih=>
    cases i with|zero=> rwa [gathering]|succ i=>
    intro e r he; rw [gathering_next]; dsimp only; unfold wake; rw [ih i (by omega) _ _ (by omega),nova, Finset.sum_eq_zero, add_zero,smul_zero]; intro u hu; apply Finset.sum_eq_zero; intro v hv; apply Finset.sum_eq_zero; intro w hw
    have h:= mem_antidiagonal.mp hu; have hP:=mem_antidiagonal.mp hv; have h':=mem_antidiagonal.mp hw
    by_cases H:u.1%2=(w.1+1)%2; · exact light_close_right G (ih _ (by omega) _ _ (by omega))
    exact light_close_left G (ih _ (by omega) _ _ H)
variable {K:KernelChoices}{W:Patch}
lemma clan_even {F:bore G}(h: Platinum F)(Q:ChartRatio G) : Platinum (clan Q W K F):= by
   intro i j hi; unfold clan compote; split; rfl; rw [h i j hi,hoist_empty,if_neg (by omega),if_neg (by omega)]; simp
lemma caravan_even {F:bore G}(h: Platinum F)(U:Stairs G W.L)(B:Bed)(Q:ChartRatio G): Platinum (caravan Q W K F U B.metric):= by
   intro i j hi; unfold caravan kiss mintage; split_ifs with hu hv; · rfl
   · unfold kin; rw [dif_neg (by omega)]
   unfold massaged; rw [Finset.sum_eq_zero (fun j _=> gathering_even (clan_even h Q) j _ _ hi),hoist_empty,neg_zero]
lemma flare_even (G:Gauge) : Platinum (flare G):= fun _ _ h=> if_neg (by omega)
lemma near_charge {w:Pow} (h:Uniform w)(hp:QuietPower w): QuietPower (rotate w) ∧ pin (PowerSeries.X*rotate w) 0=0 ∧ pin (PowerSeries.X*rotate w) 1=1 ∧ pin (PowerSeries.X*rotate w) 2=0 := by
   have he:= quiet_rotate h hp; refine ⟨he,?_,?_,?_⟩ <;> try simp only [pin] ;
   all_goals first| (rw [← pow_one (PowerSeries.X:Pow), coeff_X_pow_mul']; norm_num <;> first| exact rotate_zero w| exact he _ (by norm_num)) |simp
   simpa [Uniform, coeff_zero_eq_constantCoeff] using rotate_zero w
end
end YM.Contacts.Milling.Resetter
