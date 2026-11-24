import YM.X.Journey.Press
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
open Pert.Position Maxwell Maxwell.Free Bare Function Pert.RawLabels
variable {F:Labels.Frames G}(S:Bare.Shop F) (w:Floor R)
local notation "E"=> Pert.Position.E F
local notation "A"=> F.level d
local notation "L"=> Labels.Label G d
local notation "E₀"=> epsilon q k
open Subcell Mixed
variable {m:ℕ}(t:Test m)(hq:1<q.val)(P:Fin m→LatticePT.Word G) (j:ℕ)
local notation "r"=> epsilon q k
local notation "Fℕ"=>(atTop:Filter ℕ)
-- tally fork canonical. linear
variable [AddCommGroup V][Module ℂ V]
lemma tallyL (W: (Fin m→ Site (side q k)) → alma V m): ∃ T: alma V m,∀ p, T p=tallyM t q k (fun x=> W x p):= by
    let a:= ((origins q k).card:ℝ)⁻¹; let c:=Complex.ofReal a; let b:= r^(4*m); let u:=Complex.ofReal b; let T (z:Native q k)(v:Grid.offsets q m k):alma V m:= score r t (Grid.sample q k v) • W (fun j=>v j+z); refine ⟨c • (∑ i∈origins q k,u • (∑ v:Grid.offsets q m k,T i v)),fun p=> ?_⟩; unfold tallyM payL T; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),MultilinearMap.smul_apply,MultilinearMap.sum_apply,MultilinearMap.smul_apply,MultilinearMap.sum_apply,MultilinearMap.smul_apply];rfl
lemma tally_add (f g:(Fin m→ Site (side q k))→ℂ): tallyM t q k (f+g)=tallyM t q k f+tallyM t q k g:= by unfold tallyM payL;simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib,smul_add]
lemma tally_sub (f g:(Fin m→ Site (side q k))→ℂ): tallyM t q k (f-g)=tallyM t q k f-tallyM t q k g:= by unfold tallyM payL;simp only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,smul_sub]
lemma tally_sum (v:Finset I)(f: I→(Fin m→ Site (side q k))→ℂ):tallyM t q k (∑ i∈v,f i)=∑ i∈v,tallyM t q k (f i):= by induction v using Finset.induction_on with| empty=> simp [tallyM,payL] | insert i v h ih=> rw [Finset.sum_insert h,Finset.sum_insert h,tally_add,ih]
variable {x:Grid.offsets q m k}{p:Native q k}
abbrev storefront {m:ℕ}(q:ℕ+)(k:ℕ)(v:Grid.offsets q m k)(p:Native q k) (i:Fin m):= v i+p
lemma sake (f:Points m→ℝ): polynomialTop P q k (f ∘ points) j= ∑ i∈origins q k, ∑ v:Grid.offsets q m k, ((origins q k).card:ℝ)⁻¹ * (f (Grid.sample q k v) * rowP (storefront q k v i) P r j):= by unfold polynomialTop; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _=>Finset.sum_congr (by ext; simp) fun x _=>?_); rw [← Finset.mul_sum,Mixed.price,Grid.sample_eq,mul_assoc];apply congr_arg;apply congr_arg (fun v:ℝ=> f (points (point q k ∘ x))*v); refine Finset.sum_congr (by ext; simp) (fun j _=>?_); rfl
lemma passions : Bare.Shop.series P q k t j=tallyM t q k (fun x=> spirit x (epsilon q k) P j):= by
    let f:=Complex.re ∘ t; let g:=Complex.im ∘ t; let w:=bumpV r m; unfold Bare.Shop.series;rw [sake,sake]; unfold tallyM payL; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),Complex.ofReal_sum,Complex.ofReal_mul, Finset.smul_sum,Finset.mul_sum]; simp_rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun v _=>?_; unfold score spirit; let b:= Complex.ofReal (r^(4*m)); let A':ℂ:= ↑(((origins q k).card:ℝ)⁻¹); let L':= Complex.ofReal (rowP (storefront q k v i) P r j); let u:=Grid.sample q k v; let F₁:ℂ:= ↑(sweep f r u); let F₂:ℂ:= ↑(sweep g r u); change A'*(F₁*L') + Complex.I*(A'*(F₂*L'))= A' * (b * ((F₁+Complex.I*F₂)*(b⁻¹ * L'))); have he:b≠0:= positive_cash m k; field_simp <;> ring
local notation "Θ" x=> outerV S r x d j
lemma full_lens (p:Fin m→ Labels.Label G d): S.full q k d t j p= tallyM t q k (fun x=> (Θ x) p):= by
    obtain ⟨T,h⟩:= tallyL t (fun x=> outerV S r x d j); rw [←h]; have he : S.full q k d t j=T:= by apply Module.Basis.ext_multilinear (fun _=> (F.level d).basis); intro v; let p:=(F.level d).basis ∘ v; change S.full q k d t j p=T p; rw [h]; unfold p; simp_rw [outer_basis]; exact (spread_eval ..).trans (passions ..)
    rw [he]
lemma bank_time (p:Fin m→ E d): S.bank q k d j m t p= tallyM t q k (fun x=> outerK S r x d j p):= full_lens S t j _
lemma member_kin (b:Buffer F d)(p:Fin m→ E d): (S.bank q k d 1 m t-passV (bufferL F b) (S.bank q k d 0 m t)) p=tallyM t q k (fun x=> kin S x r b p):= by
    simp_rw [kin,MultilinearMap.sub_apply,pass_view,bank_time,←tally_sum]; exact (tally_sub t (fun x=> outerK S r x d 1 p) _).symm.trans (congr_arg _ (by ext1 a; rw [Pi.sub_apply,Finset.sum_apply])) -- reversed
end YM.PositionX.Pulse
