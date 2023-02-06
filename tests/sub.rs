#[no_mangle]
pub extern "C" fn test(a: i32, b: i32) -> i32 {
	return a + b;
}
