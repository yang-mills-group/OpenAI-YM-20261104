import YM.Integration.WilsonMeasuredPublicEntranceBranchGap

/-! A physical field known on a nonnegative real ray modulo the fixed vacuum
is fixed by an isometry of its actual reflected two-point form. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePositiveRay
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free PertExtension.Rigidity.Positive
open scoped Classical Topology

theorem fixed {E:Type*}[AddCommGroup E][Module ℂ E](T:Module.End ℂ E)(one x:E)
    (qu:T one=one)(mass:E→ℝ)(pd:∀v:E,v≠0→0 < mass v)
    (para:∀u v,mass (u+v)+mass (u-v)=2*(mass u+mass v))
    (square:∀(s:ℝ)(v:E),mass ((s:ℂ)•v)=s^2*mass v)(iso:∀v,mass (T v)=mass v)
    {s : ℝ} (hs : 0 ≤ s) {k : ℂ} (ray : T x = (s : ℂ) • x + k • one) : T x = x := by
  let v:=T x-x
  apply sub_eq_zero.mp
  change v=0
  by_contra ne
  have grows:T v=(s:ℂ)•v:=by
    change T (T x-x)=(s:ℂ)•(T x-x)
    calc T (T x-x)=(s:ℂ)•T x+k•one-T x:=by
            rw [map_sub,congrArg T ray,map_add,map_smul,map_smul,qu]
         _=(s:ℂ)•(T x-x):=by rw [smul_sub,ray];abel
  have pos:=pd v ne
  have sq:s^2=1:=by
    apply mul_right_cancel₀ (ne_of_gt pos)
    rw [←square,grows.symm,iso,one_mul]
  have exactScale:s=1:=by nlinarith
  have stable:T v=v:=by simpa only [exactScale,Complex.ofReal_one,one_smul] using grows
  have fwd:T x=x+v:=by dsimp only [v];abel
  have back:T (x-v)=x:=by rw [map_sub,stable,fwd,add_sub_cancel_right]
  have a:=iso x
  have b:=iso (x-v)
  rw [fwd] at a
  rw [back] at b
  linarith only [a,b,para x v,pos]

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 9000 in
theorem original (F:Final C f S)(J:ℝ→tower S)(lead:Leading F J)
    {d:ℕ}{I:Type*}{l:Filter I}[NeBot l]{r t:I→ℝ}
    (hr:Tendsto r l trail){u:ℝ}(hu:0<u)(ht:Tendsto t l (𝓝 u))(pos:∀i,0<t i)
    (Z:Module.End ℂ (D d))
    (conv:∀v,Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) v) l (𝓝 (Z v)))
    (v:D d){a:ℝ}(ha:0 ≤ a){k:ℂ}
    (ray:Z v=(a:ℂ)•v+k•(Bel C.book).unit d):Z v=v:=by
  obtain ⟨native,keeps⟩:=WilsonMeasuredPublicEntranceBranchGap.income F J lead hr hu ht pos Z conv
  let mass:D d→ℝ:=fun x=>positive C.labels (hierarchy C.labels) x x
  have pd (x:D d)(h:x≠0):0 < mass x:=positive_def C.labels (hierarchy C.labels) h
  have para (x y:D d):mass (x+y)+mass (x-y)=2*(mass x+mass y):=by
    dsimp only [mass]
    simp only [map_add,map_sub,LinearMap.add_apply,LinearMap.sub_apply]
    ring
  have scale (s:ℝ)(y:D d):mass ((s:ℂ) • y)=s^2*mass y:=by
    dsimp only [mass]
    simp only [Complex.coe_smul,map_smul,LinearMap.smul_apply,smul_eq_mul]
    ring
  exact fixed (E:=D d) Z ((Bel C.book).unit d) v native.neutral mass pd para scale keeps ha ray
end YM.Integration.WilsonMeasuredPublicEntrancePositiveRay

