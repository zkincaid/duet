int strlen_benchmark(char *s)
{
	char *a = s;
	for (; *s; s++);
	return s-a;
}