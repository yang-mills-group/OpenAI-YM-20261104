import YM.X.Dial.Round
import YM.X.Bare.Uncut
/-!
# Point homogeneous canonical marks for arbitrary off-shell label. Use own weight exactly.
Also scale-field version. Signed transport.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bare
open Maxwell Maxwell.Free Lattice Wilson Pert PertExtension LatticePT Stems Function Filter MeasureTheory Metric
open Next.Rank Normal MvPolynomial Labels Submodule Extra.FD Dial
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{d e k:ℕ} {V:Type*}[AddCommGroup V][Module ℂ V] {F:Labels.Frames G} (K : Shop F)
set_option quotPrecheck false
local notation "I"=> (F.level d).Index
local notation "L"=>Label G d
local notation "E"=> (Maxwell.freeTable F).Field d
local notation "W"=> LatticePT.Word G
abbrev useWord{d:ℕ} (i:(F.level d).Index):= born F K.H K.S K.hS K.hP i
def common (φ: W→V)(d:ℕ): Label G d →ₗ[ℂ] V:= (F.level d).basis.constr ℂ (fun i => φ (useWord K i))
lemma common_name (φ:W→V)(i:I) : common K φ d ((F.level d).basis i)=φ (useWord K i):=(F.level d).basis.constr_basis ..
lemma common_scale (φ:W→V)(p:L)(h:d≤e): common K φ e (raiseLabel G h p)=common K φ d p:= by
    apply LinearMap.congr_fun (f:=common K φ e ∘ₗ raiseLabel G h); apply (F.level d).basis.ext; intro i; obtain ⟨j,hj⟩:= Horizon.reference_rises F h i
    rw [LinearMap.comp_apply,hj,common_name,common_name]; exact Eq.symm (congr_arg φ (re_born F K.H K.S K.hS K.hP (congr_arg (fun p:Label G e=> p.val) hj)))

lemma base_weight_val (i:(F.level d).Index): (Grow.labelledP (useWord K i)).val=((F.level d).basis i).val:= congr_arg (fun p:L=>p.val) (base_raises F i) -- remove param
lemma use_weight (i:(F.level d).Index) : (useWord K i).d = wt F i:= rfl

def raw (d n:ℕ): Label G d→ₗ[ℂ] Curly G:= common K (fun i=>bookMark i n) d
def self (d:ℕ): Label G d→ₗ[ℂ] Curly G:= common K Grow.looking d
def slots (d n:ℕ): Label G d→ₗ[ℂ] Normal.poly (Grow.Film G n):= common K (Grow.world n) d
lemma raw_name (n:ℕ)(i:I): raw K d n ((F.level d).basis i) = bookMark (useWord K i) n := common_name ..
lemma self_name (i:I): self K d ((F.level d).basis i) = Grow.looking (useWord K i):= common_name ..
lemma slots_name (n:ℕ)(i:I): slots K d n ((F.level d).basis i)= Grow.world n (useWord K i):= common_name ..
lemma assigns_slots (x:L)(n:ℕ): Grow.assignP n (slots K d n x)= self K d x:= by apply LinearMap.congr_fun (f:=(Grow.assignP n).toLinearMap ∘ₗ slots K d n); apply (F.level d).basis.ext; intro i; change Grow.assignP n (slots K d n _)=_; rw [slots_name,self_name]; exact Grow.loom_eq ..

section rotate
variable (s:Signed)
lemma tell_coarse (n j :ℕ)(i : (F.level n).Index)(h:wt F i=d)(p:Label G d)(he: p.val=((F.level n).basis i).val): raw K n j ((F.level n).basis i)=coarse (K.S d) (K.hS d) (K.hP d) j p:= by
     subst d; rw [raw_name]; rw [←coarse_word, show p = _ from Subtype.ext (he.trans (base_weight_val K i).symm)];rfl
lemma rare (p:L)(b:ℕ)(h: p∈Labels.Grade (d,b))(j:ℕ): raw K d j p= coarse (K.S d) (K.hS d) (K.hP d) j p:= by
    rw [← (F.level d).basis.sum_repr p,map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,map_smul]; by_cases hv:(F.level d).grades i=(d,b)
    · rw [tell_coarse (K:=K) d j i (congr_arg Prod.fst hv) _ rfl]
    rw [show (F.level d).basis.repr p i=0 from (F.level d).power_coefficient i (Ne.symm hv) h,zero_smul,zero_smul]
lemma rare_spin (p:L)(j:ℕ): relay s (raw K d j p)=raw K d j (Labels.tensor s.ortho p):= by
    apply LinearMap.congr_fun (f:=(relay (R:=ℤ) s).toLinearMap ∘ₗ raw K d j) (g:= raw K d j ∘ₗ Labels.tensor s.ortho); apply (F.level d).basis.ext; intro i
    let v:=wt F i; let q: Label G v:= Grow.labelledP (useWord K i); let Q:Label G d := raiseLabel G ((F.level d).bound i) q; let B:= ((F.level d).grades i).2
    rw [show (F.level d).basis i=Q from (base_raises F i).symm]; have he(t: Label G v):raw K d j (raiseLabel G ((F.level d).bound i) t)=raw K v j t:= common_scale ..
    change relay s (raw K d j (raiseLabel G ((F.level d).bound i) q))=raw K d j (raiseLabel G ((F.level d).bound i) (tensor s.ortho q))
    have hp:q∈ Grade (v,B):= by change pureDegree q.val v B; rw [show q.val= _ from base_weight_val K i]; exact (F.level d).pure i
    rw [he, he, rare K q B hp, rare K (tensor _ _) B (keeps_grade _ _ hp _)]; exact coarsen ..
end rotate
-- at through d. engineering scaled
abbrev upoff (s:ℂ)(d:ℕ) := scaledPol (F.level d) (fun a=>s^a.1)
lemma zoomed (c:ℂ) (i:I) : upoff (F:=F) c d ((F.level d).basis i) = c ^ wt F i • ((F.level d).basis i):= scalePol_pure F _ _ ((F.level d).pure i)
def held (r:ℝ)(n z:ℕ): Label G n →ₗ[ℂ] Curly G:= raw K n z ∘ₗ (upoff (F:=F) (r:ℂ) n)
lemma held_name (r:ℝ)(z:ℕ)(i:I): held K r d z ((F.level d).basis i)= (r:ℂ)^wt F i • bookMark (useWord K i) z:= by rw [held,LinearMap.comp_apply,zoomed,map_smul,raw_name]
lemma held_spin (r:ℝ)(s:Signed)(p:L)(z:ℕ): relay s (held K r d z p)= held K r d z (tensor s.ortho p):= by
     let f(i:ℕ×ℕ):=(r:ℂ)^i.1; have he:= scalePol_commute (F:=F) (A:=F) f f (tensor s.ortho (d:=d) (G:=G)) (fun m p h=> keeps_grade m p h s.ortho) (fun _=>rfl)
     rw [held,LinearMap.comp_apply, rare_spin, LinearMap.comp_apply]; exact congr_arg _ (LinearMap.congr_fun he p).symm
end YM.PositionX.Bare
