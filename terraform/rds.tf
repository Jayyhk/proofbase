# tells rds which subnets it can put the db in
resource "aws_db_subnet_group" "main" {
  name = "proofbase"
  subnet_ids = data.aws_subnets.default.ids
}

# the postgres db. only the app instance can reach it
resource "aws_db_instance" "main" {
  identifier = "proofbase"
  engine = "postgres"
  engine_version = "18"
  # 2 vCPU, 1GB ram
  instance_class = "db.t4g.micro"
  allocated_storage = 20
  storage_type = "gp3"
  db_name = var.db_name
  username = var.db_username
  password = var.db_password
  db_subnet_group_name = aws_db_subnet_group.main.name
  vpc_security_group_ids = [aws_security_group.db.id]
  publicly_accessible = false
  skip_final_snapshot = true
}
