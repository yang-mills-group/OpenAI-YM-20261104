import YM.AveragedStep.Parcel.Sail
import YM.Push.STATIONARY_UNIFORM.Resolvent
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Lattice RG Wilson Function MeasureTheory Filter Loops RG.Patch Push.Uniform Finset
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c f:Side}(S:StepData c f)

-- all reads starting points, lifts keep repetition in hook

def land (a:Parcel c f):Finset (Rim c f):=univ.filter fun z=>∃ i, hook S a i=some z
def owners (e:Rim c f) := univ.filter fun p:Parcel c f=> e∈land S p
def home (e:Rim c f):= insert e ((owners S e).biUnion (land S))
lemma land_mem {a:Parcel c f}{i:Interior S.patch}{z}(h:hook S a i=some z): z∈land S a:= mem_filter.mpr ⟨mem_univ _,i,h⟩
lemma own_member {a:Parcel c f}{z}(h:z ∈ land S a):a∈owners S z:=mem_filter.mpr ⟨mem_univ _,h⟩
lemma own_need {a:Parcel c f}{z}(h:a∈owners S z):z∈land S a:=(mem_filter.mp h).2
lemma home_owner {e z:Rim c f}{a}(h:a∈ owners S e)(hh:z∈land S a):z∈home S e:= Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a,h,hh⟩)
lemma home_self (e:Rim c f):e∈home S e:= Finset.mem_insert_self _ _

def aperture (P:Patch) : ℕ:= (domain P).sup (fun x=>(route 0 x 1).length)
lemma reach_land (a : Parcel c f){e}(h:e∈land S a): separation (point S a) (atRim S e)≤ aperture S.patch:=by
 obtain ⟨i,h⟩:=(mem_filter.mp h).2
 cases i with
 | some v=>
   simp only [hook,Option.some.injEq] at h; subst e
   let b:=point S a; let z:=v.val.1
   have he: stop (0:Site f) (route 0 z 1)=wrap f z:=by
      have hi:=wrap_stop_cover (n:=f) (0:Cover) (route 0 z 1)
      rw [route_end,map_zero] at hi; exact hi.symm
   change separation b (wrap f z+b) ≤ _
   rw [add_comm,← he,← Loops.stop_add,add_zero]
   refine (Push.Uniform.stop_length b _).trans (Finset.le_sup (f:=fun x=>(route 0 x 1).length) v.prop)
 | none=>
   unfold hook header at h; rcases a with a|⟨a,_|x⟩
   · cases h
   · cases h
   · change some (Sum.inr (a,x))=some _ at h; rw [← Option.some.inj h]; exact (separation_self ..).le.trans (Nat.zero_le _)
lemma reach_home (e:Rim c f){z}(h:z∈home S e):separation (atRim S e) (atRim S z)≤ 2*aperture S.patch:=by
 rcases mem_insert.mp h with he|he; · subst z; simp
 obtain ⟨p,hp,hz⟩:= mem_biUnion.mp he
 apply (separation_triangle _ (point S p) _).trans
 rw [two_mul,separation_comm (atRim S e)]; exact Nat.add_le_add (reach_land _ _ (own_need S hp)) (reach_land _ _ hz)

-- coordinate multiplicities and expenses
lemma multiplicity_by {I D:Type} [Fintype I] [Fintype D](i:I→Site f)(q:I→D)
    (hi: Injective fun x=> (i x,q x)):Multiplicity i (Fintype.card D) := by
 intro z; exact (Finset.card_le_card_of_injOn q (t:=univ) (by simp) (fun x hx y hy he=>hi (Prod.ext
    (((mem_filter.mp (show x∈univ.filter _ from hx)).2).trans ((mem_filter.mp (show y∈univ.filter _ from hy)).2).symm) he))).trans_eq (card_univ)

def rimCount:=Fintype.card (Axis⊕Axis)
def parcelCount:= Fintype.card Mold
lemma rim_multiplicity:Multiplicity (atRim S) rimCount:= multiplicity_by (atRim S) (Sum.map Prod.snd Prod.snd) <| by
 intro x y; rcases x with ⟨p,x⟩|⟨q,x⟩ <;> rcases y with ⟨p',y⟩|⟨q',y⟩
 all_goals simp [atRim, S.ratio.embed_injective.eq_iff]
lemma parcel_multiplicity:Multiplicity (point S) parcelCount:= multiplicity_by (point S) sort <| by
 intro x y; rcases x with ⟨p,x⟩|⟨q,x⟩ <;> rcases y with ⟨p',y⟩|⟨q',y⟩
 all_goals simp [point, sort, S.ratio.embed_injective.eq_iff]
def cap (k n:ℕ):ℕ:= (k+k+1)^4*n
lemma cap_estimate {I:Type} [Fintype I] (a:I→Site f){k n:ℕ}{s:Finset I}{x:Site f}(h:∀ i∈s,separation x (a i)≤k)(he:Multiplicity a n):s.card ≤ cap k n:=by
 let T:=halo k ({x} : Lattice.Support f)
 let H(y:Site f):=univ.filter fun i:I=>a i=y
 have hh:s⊆ T.biUnion H:= fun i hi=> mem_biUnion.mpr ⟨_,halo_spec.mpr ⟨x,mem_singleton_self _, h i hi⟩,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩
 have ht : T.card≤(k+k+1)^4:=by simpa only [card_singleton,one_mul] using Lattice.Corona.halo_size {x} k
 exact ((card_le_card hh).trans card_biUnion_le).trans ((sum_le_sum (s:=T) (f:=fun i=>(H i).card) (fun i _=>he i)).trans (by simpa [cap] using Nat.mul_le_mul_right n ht))
lemma owned (e:Rim c f):(owners S e).card ≤ cap (aperture S.patch) parcelCount:=cap_estimate (point S) (x:=atRim S e) (by intro i hi; rw [separation_comm]; exact reach_land S i (own_need S hi)) (parcel_multiplicity S)
lemma home_count (e:Rim c f):(home S e).card ≤ cap (2*aperture S.patch) rimCount:=cap_estimate (atRim S) (x:=atRim S e) (fun _ hi=>reach_home S e hi) (rim_multiplicity S)
end YM.AveragedStep
