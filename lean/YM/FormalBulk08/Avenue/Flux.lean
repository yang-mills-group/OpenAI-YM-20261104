import YM.FormalBulk08.Avenue.Grail
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

/- Integrating the fine completion of joint quadratic against generalized
coarse inverse fills a generalized inverse (not canonical same gauge).
Even if there are zero symbols at p=0, only transverse *curl tensors*
will be carried across.
-/
open Tree
private lemma block_blend {α β:Type*}[Fintype α][Fintype β][DecidableEq α][DecidableEq β]
    (B : Matrix α α ℝ) (M : Matrix β α ℝ)(E T:Matrix α α ℝ)(V:Matrix α β ℝ)(Z U:Matrix β β ℝ)(k:ℝ)
    (hb:Bᵀ=B)(he:E=B+k • (Mᵀ*M))(h:E*T=1)(hm:E*V=k • Mᵀ)(hp:Vᵀ*B*V+k • ((1-M*V)ᵀ*(1-M*V))=Z)(hr:Z*U*Z=Z):
    B*(T+V*U*Vᵀ)*B=B:= by
    let S:=1-M*V
    have hT:Eᵀ=E:= by simp [he,hb]
    have hz: B*V= Mᵀ*(k • S):= by
       rw [he, Matrix.add_mul, Matrix.smul_mul,Matrix.mul_assoc Mᵀ] at hm;unfold S; rw [eq_sub_of_add_eq hm, Matrix.mul_smul,Matrix.mul_sub,Matrix.mul_one,smul_sub]
    have hz':Z=k • S:= by
       change Vᵀ*B*V+k • (Sᵀ*S)=Z at hp
       rw [←hp,Matrix.mul_assoc,hz, Matrix.mul_smul, Matrix.mul_smul,← smul_add,← Matrix.mul_assoc,← Matrix.transpose_mul,← Matrix.add_mul]; rw [show (M*V)ᵀ+Sᵀ=1 from (Matrix.transpose_add ..).symm.trans (by unfold S; rw [add_sub_cancel, Matrix.transpose_one]),Matrix.one_mul]
    rw [←hz'] at hz
    have hZ : Zᵀ=Z:= by rw [←hp]; simp [hb,Matrix.mul_assoc]
    have hx : Vᵀ*B=Z*M:= by nth_rw 1 [←hb]; rw [← Matrix.transpose_mul,hz,Matrix.transpose_mul,hZ,Matrix.transpose_transpose]
    have ht:V=k • (T*Mᵀ):= by
       have hh:= mul_eq_one_comm.mp h
       calc
          V=T*(E*V):= by rw [← Matrix.mul_assoc,hh,Matrix.one_mul]
          _ = k • (T*Mᵀ):= by rw [hm,Matrix.mul_smul]
    have hg:B*T*B=B-Mᵀ*Z*M:= by
       have hb: B=E-k •(Mᵀ*M):= by rw [he]; simp
       nth_rw 2 [hb]
       rw [Matrix.mul_sub,Matrix.mul_assoc B T E, mul_eq_one_comm.mp h,Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc _ Mᵀ, ← Matrix.smul_mul, Matrix.mul_assoc B,← Matrix.mul_smul,←ht,hz]
    rw [Matrix.mul_add, Matrix.add_mul,← Matrix.mul_assoc B (V*U), ←Matrix.mul_assoc B V, Matrix.mul_assoc _ Vᵀ B,hx,hz, hg]; simp only [Matrix.mul_assoc]; rw [←Matrix.mul_assoc U,←Matrix.mul_assoc Z,←Matrix.mul_assoc Z,hr]; abel
private lemma reduce_span {α β:Type*}[Fintype α][Fintype β][DecidableEq α][DecidableEq β](H:Matrix α α ℝ)(Q:Matrix α β ℝ)(p:Matrix β α ℝ)(Z:Matrix β β ℝ)(hs:Hᵀ=H)(he:H*Q*p=H)(hv:Qᵀ*H*Q*Z*(Qᵀ*H*Q)=Qᵀ*H*Q): H*(Q*Z*Qᵀ)*H=H:= by
    have hh:pᵀ*Qᵀ*H=H:= by
       have hx:= congr_arg Matrix.transpose he; rw [Matrix.transpose_mul,Matrix.transpose_mul,hs] at hx; rw [Matrix.mul_assoc,hx]
    calc H*(Q*Z*Qᵀ)*H = pᵀ*(Qᵀ*H*Q*Z*(Qᵀ*H*Q))*p := by rw [← Matrix.mul_assoc pᵀ,← Matrix.mul_assoc pᵀ,← Matrix.mul_assoc pᵀ,← Matrix.mul_assoc pᵀ,hh]; simp only [← Matrix.mul_assoc]; have he':=congr_arg (fun x=> (H*Q*Z*Qᵀ)*x) he; simp only [← Matrix.mul_assoc] at he'; exact he'.symm
         _ = H := by rw [hv,← Matrix.mul_assoc, ←Matrix.mul_assoc,hh,he]
variable {u:ℕ}{K: KernelChoices} (P:Flight j u)(L: Flat.Lodge P.patch)(hp:P.patch.Branches K G)(n:Side)
open scoped Matrix
abbrev tranks (K:KernelChoices):= primary P.patch K n
abbrev flora (K:KernelChoices):= Reef.floor K P L n
lemma through_tor (hu:4≤u):
   let S:=primary P.patch K n; let F:=Reef.floor K P L n;
   let _Z:= kernelP G K.penalty P.land n; let H:= kernelP G K.penalty P.wing (n*P.patch.L); let U:= bandR G P.land K.penalty n; let X:=puppet P hp L n; let _T:=testPrecision G S F P.wing; let Y:=pMean G K P n F; let Q:=(dropRoot G S F)ᵀ
   H*(Q*(X+Y*U*Yᵀ)*Qᵀ)*H=H:= by
    intro S F Z H U X T Y Q;let M:=patron G (Precision.probe S);let B:=Qᵀ * H * Q; let C:=M*Q
    have he:= Flat.normal (K:=K) G P n F hu; change T*Y= _ ∧ (Q*Y)ᵀ*H*(Q*Y)+K.penalty • ((1-M*(Q*Y))ᵀ*(1-M*(Q*Y)))=Z at he
    have hT : T=B+K.penalty • (Cᵀ*C):= rfl
    have hZ: Yᵀ*B*Y+K.penalty • ((1-C*Y)ᵀ*(1-C*Y))=Z:= by rw [←he.2]; simp only [B,C,Matrix.transpose_mul,Matrix.mul_assoc]
    have hH:Hᵀ= H:= kernel_color _ K.penalty_pos P.legal
    have hb:Bᵀ=B:= by simp only [B,hH,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
    have hv:=block_blend B C T X Y Z U K.penalty hb hT (honey P hp L n).2 he.1 hZ (generalized _ K.penalty_pos hu)
    refine reduce_span H Q (hang G S F * (butt G n (n*P.patch.L))ᵀ) _ hH ?_ hv
    have he : Q*hang G S F=imprint G S F:= inject_out _
    rw [← Matrix.mul_assoc,Matrix.mul_assoc H Q, he, imprint,Matrix.mul_add, ← Matrix.mul_assoc H (patron G (d 0 (n*P.patch.L)))]
    rw [show H*patron G (d 0 (n*P.patch.L)) = 0 from ?_, Matrix.zero_mul, add_zero, Matrix.mul_assoc, (reproduced (G:=G) ..).1, Matrix.mul_one]; unfold H kernelP; rw [← patron_mul, Precision.K_kills, patron_zero]
lemma splits (hu:4≤u):
   let S:=primary P.patch K n; let F:=Reef.floor K P L n; let Z:= Reef.force G (n*P.patch.L); let U:= bandR G P.land K.penalty n; let V:=bandR G P.wing K.penalty (n*P.patch.L); let X:=puppet P hp L n; let Y:=pMean G K P n F; let Q:=(dropRoot G S F)ᵀ
   Z*V*Zᵀ= Z*(Q*(X+Y*U*Yᵀ)*Qᵀ)*Zᵀ := by
   intro S F Z U V X Y Q; let A:=kernelP G K.penalty P.wing (n*P.patch.L)
   have he: A*V*Zᵀ= Zᵀ:= invite _ K.penalty_pos P.legal
   have h:Aᵀ=A:=kernel_color _ K.penalty_pos P.legal
   have hv:Vᵀ=V:= by unfold V bandR; rw [← patron_star, cargo_sym K.penalty _ K.penalty_pos]
   have ht:= congr_arg Matrix.transpose he; rw [Matrix.transpose_mul,Matrix.transpose_mul,h,hv,Matrix.transpose_transpose, ← Matrix.mul_assoc] at ht
   let D:=Q*(X+Y*U*Yᵀ)*Qᵀ
   have hx : A*D*A=A:=through_tor P L hp n hu
   symm; change Z*D*Zᵀ= _; calc
       _ = (Z*V*A)*D*(A*V*Zᵀ):= by rw [he,ht]
       _ = Z*V*A*V*Zᵀ:= by rw [Matrix.mul_assoc (Z*V) A]; simp only [Matrix.mul_assoc]; apply congr_arg (Z * ·); apply congr_arg (V * ·); have hu:= congr_arg (·*(V*Zᵀ)) hx; simp only [Matrix.mul_assoc] at hu; exact hu
       _ = _:= by rw [ht]
end YM.FormalBulk08.Avenue
