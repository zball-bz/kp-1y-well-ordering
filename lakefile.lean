import Lake
open Lake DSL
package kp1y where
  leanOptions := #[⟨`autoImplicit, false⟩]
require YesMetaZFC from "third_party/YesMetaZFC"
@[default_target]
lean_lib KP1Y
