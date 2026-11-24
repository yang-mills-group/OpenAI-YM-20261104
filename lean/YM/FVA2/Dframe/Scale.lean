import YM.FVA2.Dframe.Rates
/-! # Exact scale factors and launches. Uncompressed point version at a regulator -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Dframe
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
section words
variable {n d k:ℕ}{G:Gauge}
variable (ν:ℝ) (Y:XSpace.Initialize G) (S:Prescription (Press.portDeck G))
local notation "Π"=> Press.portDeck G
local notation "M"=> Toon G
local notation "L"=> M d
local notation "W"=> Fin n
local notation "A"=> Sample n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
variable (a: Sample n) (t:Fin n→Toon G d)
abbrev Story (t:Fin n→Toon G d):= (i:W)→ Toon G (t i).size
abbrev Ufee (m:Mesh)(e:ℕ):ℂ:= (m.spacing:ℂ)⁻¹ ^ e
abbrev Csum (m:Mesh)(t:Fin n→ℕ):ℂ:= (∏ j:W,Ufee m (t j))
abbrev interest (v:Story t) : W→ℕ:= fun i=> (v i).size
abbrev piston (v: Story t) : W→ℕ:= fun i=> (t i).size-(v i).size
local notation "sF"=> a.F
local notation "z"=> Ufee a.F
local notation "w"=> Csum a.F
lemma flash_time : Vane.charge ( Rake.Label.h ∘ flash ∘ t ) Finset.univ=∑ i:W,(t i).size:=rfl
lemma clockV : ((a.F.spacing:ℂ)^( Vane.charge ( Rake.Label.h ∘ flash ∘ t ) Finset.univ ))⁻¹=w ( fun i=> (t i).size ):= by rw [flash_time, ← inv_pow, ← Finset.prod_pow_eq_pow_sum ]; -- reversed
lemma currency (v:Story t) : w (piston t v)*w (interest t v)=w (fun i=> (t i).size):= by unfold Csum; rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun i _=> Eq.trans (pow_add (a.F.spacing:ℂ)⁻¹ ((t i).size-(v i).size) (v i).size).symm (congr_arg _ (Nat.sub_add_cancel (size_le (v i)))))
abbrev born (v:Story t) : List (Birth G):= Finset.univ.toList.map (fun j:W=> (⟨ (t j).size,v j,a.layout j ⟩: Arrival.Birth G))
abbrev memoir (v:Story t):= Birth.words Y a.F.p.side ( born a t v )
abbrev parent (v:Story t) : W→ Sec G d:= fun j=> up (size_le (t j)) ( theory (v j) )
local notation "ℒ"=> live Y d a
local notation "F"=> Csum a.F
lemma value_t (v:Story t) : ℒ k (parent t v)=w ( interest t v ) * Slice.record (memoir Y a t v) k:= by
    let X:= a.F; let H(i:W): HP G (v i).size:= Arrival.Birth.theory (v i); have h(i:W):( v i ).size≤d:= le_trans (size_le (v i)) (size_le (t i));
    change ℒ k (shells (interest t v) H h)=_; rw [lives Y d _ _ h, Initialize.atTuple_eq ]; -- spacing pulled
    let p := Y.tree a.F.p; let R i:= On.stencil Y.hol ( Y.surveys (v i).size ) a.F.p p ( Lattice.wrap a.F.p.side ( a.layout i )) ( H i ); have he (e:Finset W) : (∏ i∈e,Y.atSite a.F ( v i).size (chartV a i) (H i))= (∏ i∈e,z (v i).size) • ∏ i∈e,R i:= by
       induction e using Finset.induction_on with
       | empty=> simp
       | insert i e hp ih=> rw [Finset.prod_insert hp,Finset.prod_insert hp,Finset.prod_insert hp,ih,Initialize.atSite,LinearMap.smul_apply,← inv_pow,mul_smul,smul_mul_assoc,mul_smul_comm]; rfl
    have ht: XSpace.Bare.normalized p G (∏ i:W,R i)= PowerSeries.map Complex.ofRealHom ( memoir Y a t v ):= Birth.compact_labels Y p Finset.univ _ (fun i:W=> (t i).size) v
    rw [ show ∏ i,(Y.atSite a.F (interest t v i) (chartV a i)) ( H i )= _ from he Finset.univ, ht_ ( XSpace.Bare.normalized p G ), ht, map_smul, coeff_map ]; rfl -- ht_ flips from PS orientation
where ht_ (f : XSpace.Bare.Series (Y.tree a.F.p) G→ₗ[ℂ] Cn) (c:ℂ)(p: XSpace.Bare.Series ( Y.tree a.F.p ) G) : f (c • p)=c • f p:= map_smul ..
local notation "η"=> ν- Arrival.Schedule.theta a.F
abbrev reset (p:Mesh):= MS.Book.Program.shift S.team (ν - Arrival.Schedule.theta p)
abbrev orderT (a:Sample n) (d:ℕ) := substitute (reset ν S a.F) (live Y d a)
lemma translate (p:Cn)(K:T (Point G d n))(v:Tags G d n): substitute p K k v=substitute p (fun j=> K j v) k:= by simp only [rules,sum_apply,smul_apply]
lemma translate_l (v:Story t): orderT ν Y S a d k (parent t v)= w (interest t v)*substitute (reset ν S sF) (Slice.record (memoir Y a t v)) k:= by
    unfold orderT; rw [translate]; simp_rw [value_t]; rw [show (fun j=> w (interest t v)* Slice.record (memoir Y a t v) j)= (w (interest t v)) • (Slice.record (memoir Y a t v)) from rfl, map_smul,Pi.smul_apply,smul_eq_mul]
local notation "ι"=> Change.Dictionary.vertices (flash ∘ t)
abbrev fee (a:Sample n)(t:Fin n→ Toon G d):= Change.Dictionary.paid (flash ∘ t) S (ν-Arrival.Schedule.theta a.F)
abbrev allows (a:Mesh)(g:Toon G d)(x:Toon G g.size): Cn := μ (fun i:ℕ=> (stake ν S a g x i:ℝ))
abbrev ledger (v:Story t) (i:W) : Change.Dictionary.vertices (flash ∘ t):= ⟨i,v i⟩
lemma register (v: Story t)(i:W): allows ν S sF (t i) (v i)= C (z (piston t v i)) * μ (fee ν S a t (ledger t v i)) := by
    apply PowerSeries.ext; intro k; rw [coeff_C_mul]; simp_rw [allows, coeff_mk]; unfold stake; push_cast; rfl -- fee rfl
abbrev entirety (v:Story t) := μ (substitute (reset ν S sF) (Slice.record (memoir Y a t v)))
lemma value_s (v:Story t) : μ (fun j=> orderT ν Y S a d j (parent t v))=C (w (interest t v))* entirety ν Y S a t v := by apply PowerSeries.ext; intro k; simp only [entirety,coeff_C_mul,coeff_mk,translate_l]
local notation "H"=> Top.value Y (flash ∘ t) S 0 a.layout a.F.p.side (ν-Arrival.Schedule.theta sF) Finset.univ
lemma book_s : μ H=∑ i: Story t,(∏ j:W, μ (fee ν S a t (ledger t i j))) * entirety ν Y S a t i:= by
    unfold Arrival.Top.value; let x:Story t:= fun i=> read (panel (t i)); rw [ Constants.to_univ (a:=Change.Dictionary.factors (flash ∘ t)) (f:=x) ]; apply Finset.sum_congr rfl; intro i _; refine congr_arg (( ∏ j:W,μ (fee ν S a t ( ledger t i j ))) * ·) ?_; unfold entirety memoir born; -- `zero_add`
    rw [List.map_map, show (Top.declares ( flash ∘ t ) 0 a.layout ∘ Constants.ink i)= ( fun j:W=> (⟨ (t j).size,i j,a.layout j ⟩: Birth G) ) from ?_ ]; -- ν
    funext j; unfold Function.comp; dsimp only [Constants.ink,Top.declares]; rw [zero_add]
-- reservoir at all orders before position.
abbrev scaled (a: Sample n)(t: Fin n→ Toon G d) : T ℂ := fun i=> Schedule.entries ν Y (flash ∘ t) S Finset.univ i a
lemma doll : μ (scaled ν Y S a t)= C (w (fun i=> (t i).size)) * μ H:= by
    refine PowerSeries.ext fun i=>?_ ; rw [coeff_C_mul]; simp only [scaled, Schedule.entries, coeff_mk ]; rw [show (( a.F.spacing:ℂ )^_)⁻¹= _ from clockV a t]
lemma store_s : (∑ v: Story t,(∏ i, allows ν S sF (t i) (v i))* μ (fun j=> orderT ν Y S a d j (parent t v)))= μ (scaled ν Y S a t):= by
 rw [ doll ν Y S a t, book_s ν Y S a t, Finset.mul_sum ]; refine Finset.sum_congr rfl (fun i _=>?_); simp_rw [register ν S a t i, value_s, Finset.prod_mul_distrib, ← _root_.map_prod ]; let a1:= C (w (piston t i)); let a2:= C (w (interest t i)); let b1:= ∏ j:W,μ (fee ν S a t (ledger t i j)); let r:= entirety ν Y S a t i; rw [ ← currency a t i, map_mul ]; change a1*b1*(a2*r)= a1*a2*(b1*r); ring
end words
end YM.FVA2.Dframe
