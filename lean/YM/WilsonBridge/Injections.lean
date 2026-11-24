import YM.WilsonBridge.Inverted
import YM.WilsonBridge.Projection

/-!
# The identifications of the orbit log chart and Landau ambient fields

Real maps. Antifield terms checked separately. Matrices are complex for substitution
(push on momenta and projection to ambient logs). Counting transpose in quotient
link coordinates; fixed sites allowed and *not* doubled in the site sums in `harmonicC`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Injections
open MS MS.Book MS.Koszul MS.City MS.Native MS.Tone Lattice MS.Orbit MS.Landau
open Function Finset FiniteDFT Full Based Based.Position PertExtension Orb
open scoped BigOperators Matrix
variable {V K T:Type}[DecidableEq V][Fintype V][DecidableEq K][Fintype K][Fintype T][DecidableEq T]
variable {G:Gauge}{n:Side}
local notation "J" => Full.Glu G n
local notation "C" => Full.Ghost G n
local notation "Ja" => Position.Gluon G n
local notation "Ca" => Position.Ghost G n
local notation "Eₐ" => Position.E G n
local notation "Ω" => Position.U G n
-- avoid implicit ambiguous Lean matrix convention.
def glyph (X: Lot G V→ₗ[ℝ] Lot G K) : Matrix ( Native.Eyes G K ) ( Native.Eyes G V ) ℝ:= fun i j => projector i (X (priv j))
def symbol (X: Lot G V→ₗ[ℝ] Lot G K) : Matrix (Native.Eyes G K) (Native.Eyes G V) ℂ:= (glyph X).map ((↑) : ℝ→ℂ)
omit [Fintype V] [DecidableEq K] [Fintype K] in
lemma entry (X: Lot G V→ₗ[ℝ] Lot G K)(i j): symbol X i j=projector i (X (priv j)):=rfl
omit [Fintype V] [Fintype T] [DecidableEq T] in
lemma g_mul (X: Lot G V→ₗ[ℝ] Lot G K)(Z: Lot G K→ₗ[ℝ] Lot G T)(i: Eyes G T)(j: Eyes G V): (glyph Z * glyph X) i j= glyph (Z.comp X) i j:= by
    have he:= Native.frame (X (priv j)); change _=projector i (Z (X (priv j))); rw [← he, map_sum,map_sum]; simp_rw [map_smul]; apply Finset.sum_congr rfl; intro q _; exact mul_comm ..
omit [Fintype V] [Fintype T] [DecidableEq T] in
lemma s_mul (X: Lot G V→ₗ[ℝ] Lot G K)(Z: Lot G K→ₗ[ℝ] Lot G T): symbol Z*symbol X = symbol (Z.comp X):= by
    ext i j:1; apply Eq.trans _ (congr_arg (fun x:ℝ=>(x:ℂ)) (g_mul X Z i j)); simp_rw [symbol,Matrix.mul_apply]; push_cast; rfl
lemma s_one : symbol (LinearMap.id (R:=ℝ) (M:= Lot G V))=1:= by ext i j:1; change (projector i (priv j):ℂ)=_; rw [ Position.basis_pr ]; split <;> simp [ Matrix.one_apply, * ]
omit [Fintype V] [DecidableEq K] [Fintype K] in
lemma s_zero : symbol (0: Lot G V→ₗ[ℝ] Lot G K)=0:= by ext i j:1; simp [entry]
omit [Fintype V] [DecidableEq K] [Fintype K] in
lemma s_sum (X Z: Lot G V→ₗ[ℝ] Lot G K): symbol (X+Z)= symbol X + symbol Z:= by ext i j:1; simp [ entry ]
omit [Fintype V] [DecidableEq K] [Fintype K] in
lemma s_sub (X Z: Lot G V→ₗ[ℝ] Lot G K): symbol (X-Z)= symbol X - symbol Z:= by ext i j:1; simp [ entry ]

variable (G n)
abbrev aFull := Lot G (Edge (Site n))
abbrev cFull := Lot G (Site n)
local notation "Aᵣ" => aFull G n
local notation "Cᵣ" => cFull G n
def reverseA : Aᵣ →ₗ[ℝ] Aᵣ:= LinearMap.pi fun i:Edge (Site n)=> -(LinearMap.proj (Orb.reflect i))
def reverseC : Cᵣ →ₗ[ℝ] Cᵣ:= LinearMap.pi fun i:Site n=> LinearMap.proj (-i)
abbrev liftA := edgeField n G.Color
abbrev liftC := siteField n G.Color
def beginA : Aᵣ→ₗ[ℝ] Eₐ:= LinearMap.pi fun i:OEdge n=> LinearMap.proj i.val
def beginC : Cᵣ→ₗ[ℝ] Ω:= LinearMap.pi fun i: BasedSite n=> LinearMap.proj i.val
local notation "κᵣ" => νt n
def takeMean : Cᵣ→ₗ[ℝ] G.Color:= (κᵣ) • ∑ i:Site n, LinearMap.proj i
def takeRoot : Cᵣ→ₗ[ℝ] G.Color:= LinearMap.proj 0
def remaining : G.Color→ₗ[ℝ] Cᵣ:= LinearMap.pi fun _:Site n=> LinearMap.id
def minusRoot : Cᵣ→ₗ[ℝ] Cᵣ:= LinearMap.id - remaining G n ∘ₗ takeRoot G n
def avg : Cᵣ→ₗ[ℝ] Cᵣ:= remaining G n ∘ₗ takeMean G n
def meanless : Cᵣ→ₗ[ℝ] Cᵣ:= LinearMap.id - avg G n
def cLift : Ω→ₗ[ℝ] Cᵣ:= meanless G n ∘ₗ liftC G n
abbrev Λe := symbol (liftA G n)
abbrev Λc := symbol (cLift G n)
abbrev projectA := symbol (beginA G n)
abbrev projectC := symbol (beginC G n ∘ₗ minusRoot G n)
local notation "Aa" => liftA G n
local notation "Cc" => liftC G n
local notation "He" => Λe G n
local notation "Xc" => Λc G n
local notation "Da" => projectA G n
local notation "Rₐ" => Ra G n
local notation "Kc" => harmonicC G n
local notation "Kv" => harmonicA G n
local notation "ρ" => projectC G n
variable {G n}
lemma minA_rep (F: Aᵣ)(he:∀ i,F (Orb.reflect i)= -F i)(x:Edge (Site n)): Aa (beginA G n F) x=F x:= by
    unfold liftA; rw [edge_spec]; split_ifs with hx; · change F _=F x; congr 1
    change -F (index x).val=F x; rw [(show (index x).val= Orb.reflect x from (eR_spec x).resolve_left hx),he,neg_neg ]
lemma A_rev : Ra G n=symbol (reverseA G n):= by
    ext i j:1; rw [entry,projector_k]; change Rₐ i j=(( (-priv j (Orb.reflect i.1)) i.2 : ℝ ) :ℂ); rw [PiLp.neg_apply,← projector_k (flipA i),basis_pr, ← Full.RA_symm,Full.Ra,Matrix.transpose_apply]; unfold Reflect; split_ifs with hx <;> simp [ *, eq_comm ] at *
lemma C_rev : Rc G n=symbol (reverseC G n):= by
    ext i j:1; rw [entry,projector_k]; change Rc G n i j= (priv j (-i.1) i.2: ℂ); rw [← projector_k (flipC i), basis_pr, ← Full.RC_symm, Full.Rc, Matrix.transpose_apply]; unfold Reflect; split_ifs with hx <;> simp [ *, eq_comm ] at *
lemma equivA (he:Even n.val) : Rₐ*He=He:= by
    rw [A_rev]; unfold Λe; rw [s_mul]; apply congr_arg; apply LinearMap.ext; intro u; funext e; change - liftA _ _ u _= _; unfold liftA; rw [edge_even he,neg_neg]
lemma restrictA : Da*He=1:= by
    unfold projectA Λe; rw [s_mul,← s_one ]; apply congr_arg; apply LinearMap.ext; intro i; funext a; exact edge_rep i a
abbrev leg (i:Ja) : J:= (i.1.val,i.2)
lemma projectA_at (i:Ja)(j:J): Da i j= if leg i=j then 1 else 0:= by
    rw [ projectA, entry, show projector i (beginA G n (priv j))=projector (leg i) (priv j) from ?_, basis_pr ]; split_ifs <;> simp
    rw [projector_k,projector_k]; rfl
lemma at_leg (i j:Ja) : He (leg i) j= if i=j then 1 else 0:= by rw [Λe,entry, show projector (leg i) (Aa (priv j))=projector i (priv j) from (by simp only [projector_k,leg,liftA,edge_rep]),basis_pr ]; split_ifs <;> simp
lemma flip_leg (he:Even n.val)(i j:Ja): leg i≠flipA (leg j):= by
    intro h; have hh:i.1.val= Orb.reflect j.1.val:= congr_arg Prod.fst h; have hi:= i.1.property; rw [ hh, eR_reflect,j.1.property ] at hi; exact no_fixed_edge he _ hi.symm
lemma leg_inj : Injective (leg (G:=G) (n:=n)):= fun _ _ h=> Prod.ext (Subtype.ext (congr_arg Prod.fst h)) (congr_arg (fun x:J=> x.2) h)
lemma mirroredA (he: Even n.val): (He).transpose=Da+Da*Rₐ:= by
    ext i j:1; let P : Matrix Ja J ℂ:= Da+Da*Rₐ; have μ (j:Ja): (He).transpose i (leg j)=P i (leg j):= by
        rw [Matrix.transpose_apply, at_leg]; unfold P; rw [ Matrix.add_apply, Full.Ra,Full.reflects_right,projectA_at,projectA_at, if_neg (flip_leg he i j),zero_mul,add_zero ]; simp [leg_inj.eq_iff,eq_comm ]
    change _= P i j; suffices ∃ x:Ja, j=leg x ∨ Orb.reflect j.1=x.1.val∧j.2=x.2 by
        obtain ⟨x,h|⟨h,h'⟩⟩:=this; · rw [h]; exact μ x
        have hx : (He).transpose *Rₐ= (He).transpose:= by rw [← Full.RA_symm, ← Matrix.transpose_mul,equivA he]
        have hp : P*Rₐ=P:= by unfold P; rw [Matrix.add_mul,Matrix.mul_assoc,Full.RA2,Matrix.mul_one,add_comm]
        nth_rw 1 [← hx]; nth_rw 1 [← hp]; rw [Full.Ra, reflects_right,reflects_right,show flipA j=leg x from Prod.ext h h', μ ]
    rcases j with ⟨e,t⟩; rcases eR_spec e with h|h; · exact ⟨(⟨e,h⟩,t),Or.inl rfl⟩
    exact ⟨(⟨_,( eR_reflect e ).trans h⟩,t),Or.inr ⟨rfl,rfl⟩⟩
lemma eigenA (he:Even n.val): (He).transpose * He=1+(1:Matrix Ja Ja ℂ):= by rw [mirroredA he,Matrix.add_mul, restrictA, Matrix.mul_assoc,equivA he,restrictA]
lemma equivProjA (he:Even n.val): He * (He).transpose = 1+Ra G n:= by
    rw [mirroredA he, show Da+Da*Rₐ=Da*(1+Rₐ) from (by rw [Matrix.mul_add,Matrix.mul_one]) ]
    unfold Λe projectA; rw [ ← Matrix.mul_assoc,s_mul, ← s_one, A_rev, ← s_sum,s_mul ]; apply congr_arg; apply LinearMap.ext; intro F; funext i; refine minA_rep ((LinearMap.id (R:=ℝ) (M:=Aᵣ) + reverseA G n) F) ?_ i; intro i; change F _+ -(F (Orb.reflect (Orb.reflect i))) = -( F i+ -(F _)); rw [Orb.reflect_reflect]; abel
lemma harmonic_empty (he: Even n.val): Kv * He=0:= by
    have hr : Kv *Ra G n= -Kv:= by ext i j:1; rw [Full.Ra,reflects_right, mul_neg, mul_one]; rfl
    have hs : Kv*He= -(Kv*He):= by nth_rw 1 [← equivA he]; rw [← Matrix.mul_assoc,hr, Matrix.neg_mul]
    linear_combination (norm:=module) (1/2:ℂ) • hs

local notation "τ" => takeMean G n
local notation "μ" => avg G n
local notation "Ψ" => cLift G n
local notation "Δ" => minusRoot G n
local notation "Φ" => meanless G n
local notation "Rcc"=>Full.Rc G n
lemma actual_avg (F:Cᵣ)(i:Site n): μ F i = κᵣ • ∑ i:Site n, F i:= by change takeMean G n F=_; unfold takeMean; rw [LinearMap.smul_apply,LinearMap.sum_apply]; rfl
lemma take_const (F:G.Color) : τ (remaining G n F)=F := by
    have he : (takeMean G n) (remaining G n F)=_ := actual_avg (remaining G n F) 0
    rw [ he, show ∑ i:Site n, remaining G n F i = n.val^4 • F from ?_ ]; swap; · change (∑ _:Site n,F) = n.val ^4 • F; simp
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,Nat.cast_pow]; unfold νt; rw [inv_mul_cancel₀ (pow_ne_zero _ (show ( n.val:ℝ ) ≠0 from (Bloch.side_pos _).ne')), one_smul]
lemma meanSymbol : Kc=symbol μ:= by
    ext ⟨i,t⟩ ⟨j,u⟩:1; rw [entry,projector_k ]; dsimp only; rw [ actual_avg, show ∑ i:Site n,priv (j,u) i = Native.baseC u from (by simp [priv]) ]; change (if t=u then scaleZ n else 0)=(((κᵣ • Native.baseC u) t:ℝ):ℂ); split_ifs with h <;> simp [ *, Native.baseC,EuclideanSpace.basisFun_apply ]
lemma mean_flip : (μ).comp (reverseC G n) = μ:= by apply LinearMap.ext; intro X; funext i; rw [LinearMap.comp_apply,actual_avg,actual_avg]; exact congr_arg ( ( κᵣ ) • · ) (Equiv.sum_comp (Equiv.neg _) X)
-- along constant shifts
lemma take_less (F:Cᵣ): τ (Φ F)=0:= by unfold meanless; rw [LinearMap.sub_apply,map_sub]; change τ F-τ (remaining G n (τ F))=_; rw [take_const,sub_self]
lemma during (F:Cᵣ): Δ (Φ F)=Δ F:= by funext x; change F x-τ F -(F 0-τ F)=F x-F 0; abel
lemma rebasis (F:Cᵣ): Φ (Δ F)=Φ F:= by
    unfold minusRoot; rw [LinearMap.sub_apply,map_sub, LinearMap.id_apply, sub_eq_self]; funext i; change F 0- τ (remaining G n (F 0))=0; rw [take_const,sub_self]
lemma exactly_based (F:Ω) : beginC G n (Δ (Cc F))=F:= by funext i; change Cc F i.val-Cc F 0= _; simp [liftC]
lemma c_equivs (F:Ω)(i:Site n) : Ψ F (-i) = Ψ F i:= by change Cc F (-i)-τ _=Cc F i-τ _; unfold liftC; rw [site_even]
lemma equivC : Rcc * Xc=Xc:= by
    unfold Λc; rw [C_rev,s_mul]; apply congr_arg; apply LinearMap.ext; intro F; funext i; exact c_equivs F i
lemma no_mean : Kc * Xc=0:= by
    unfold Λc; rw [meanSymbol,s_mul, ← s_zero ( V:=BasedSite n ) ( K:=Site n ) ]; apply congr_arg; apply LinearMap.ext; intro F; funext i; exact take_less _
lemma leftC : ρ * Xc=1:= by
    unfold projectC Λc; rw [s_mul,← s_one ( V:=BasedSite n ) ]; apply congr_arg; apply LinearMap.ext; intro u; change beginC G n (Δ (Φ _))=_; rw [during,exactly_based]; rfl
lemma lift_base_eq (F:Cᵣ)(h0:F 0=0)(he:∀ x,F (-x)=F x): Cc (beginC G n F)=F:= by
    funext i; unfold liftC; rw [site_spec]; split
    next h => rw [vertex_eq_iff.mp h,h0]
    change F (vertex i)=F i; rcases vertex_spec i with h|h; · rw [h]
    rw [h,he]
lemma assumed_proj : Xc*ρ*(1+Rcc)=(1-Kc)*(1+Rcc):= by
    unfold Λc projectC; rw [meanSymbol,C_rev,s_mul,← s_one,← s_sum,← s_sub,s_mul,s_mul]; apply congr_arg; apply LinearMap.ext; intro F; let Z:= F+ reverseC G n F; change Φ (Cc (beginC G n (Δ Z)))=Φ Z; rw [lift_base_eq, rebasis]; · change Z 0-Z 0=0; rw [sub_self]
    intro i; change F (-i)+F (- -i)- Z 0= F i+F (-i)-Z 0; rw [neg_neg]; abel
lemma insideC {A:Type}(M:Matrix C A ℂ) (he:Rcc *M=M)(h0:Kc*M=0): Xc*ρ*M=M:= by
    have hh : (1+Rcc)* M=M+M:= by rw [ Matrix.add_mul,he,Matrix.one_mul]
    have hp:= congr_arg ( fun v: Matrix C C ℂ=> v * M ) (assumed_proj (G:=G) (n:=n)); rw [Matrix.mul_assoc ( Xc * ρ ),Matrix.mul_assoc ( 1-Kc ),hh, Matrix.mul_add,Matrix.mul_add,Matrix.sub_mul,h0,Matrix.one_mul,sub_zero] at hp; linear_combination (norm:=module) (1/2:ℂ) • hp
-- based gradient. X matrix
local notation "A₀"=> Aᵣ
local notation "Tg"=> (Based.Position.kinetic G n)
open MS.Bare
lemma basis_lift (he:Even n.val): Full.X G n *Xc=He*(Tg).X := by
    have ht : Xc=(1-Kc)* symbol Cc:= by rw [meanSymbol, ← s_one, ← s_sub,s_mul]; rfl
    rw [ht,← Matrix.mul_assoc,Matrix.mul_sub, Full.constants_d,Matrix.mul_one, sub_zero, show Full.X G n= symbol ( Native.Chart.roam (Native.Chart.drive n) (0:A₀)) from funext fun i=> funext fun j=> Full.ghost_X i j, show (Tg).X=symbol (based (0:Eₐ)) from rfl ]; unfold Λe; rw [s_mul,s_mul]; apply congr_arg; apply LinearMap.ext; intro F; funext i; change Maurer.volts _ _= _; rw [ show (0:A₀) i=(0:G.Color) from rfl,Maurer.volt_zero]; exact (lifted_grad F i he).symm -- needs he even!
end YM.WilsonBridge.Injections
